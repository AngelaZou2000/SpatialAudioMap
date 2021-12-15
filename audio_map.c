/*
 * File:        TFT, keypad, DAC, LED, PORT EXPANDER test
 * Direct Digital Synthesis example 
 * DAC channel A has audio
 * DAC channel B has amplitude envelope
 * Author:      Bruce Land
 * For use with Sean Carroll's Big Board
 * Target PIC:  PIC32MX250F128B
 */

////////////////////////////////////
#include "config_1_3_2.h"            // clock AND protoThreads configure!
#include "pt_cornell_1_3_2_python.h" // threading library
#include "port_expander_brl4.h"      // yup, the expander
#include "tft_master.h"              // graphics libraries, SPI channel 1 connections to TFT
#include "tft_gfx.h"
#include <stdlib.h>                  // need for rand function
#include <math.h>                    // need for sine function
#include <stdfix.h>                  // The fixed point types

////////////////////////////////////
// lock out timer interrupt during spi comm to port expander
// This is necessary if you use the SPI2 channel in an ISR
#define start_spi2_critical_section INTEnable(INT_T2, 0);
#define end_spi2_critical_section INTEnable(INT_T2, 1);

// string buffer for print statement
char buffer[60];

////////////////////////////////////
//== Audio DAC ISR =========================================================
#define DAC_config_chan_A 0b0011000000000000 // A-channel, 1x, active
#define DAC_config_chan_B 0b1011000000000000 // B-channel, 1x, active
#define Fs 44000.0 // audio sample frequency
#define two32 4294967296.0 // 2^32, constant for setting DDS frequency
float DDS_constant = 4294967296.0/44000.0; // precomputed constant for DDS increment
// sine lookup table for DDS
#define sine_table_size 256
volatile _Accum sine_table[sine_table_size] ;
// phase accumulator for DDS
volatile unsigned int DDS_phase_left;
volatile unsigned int DDS_phase_right;
volatile unsigned int car_phase_left;
volatile unsigned int car_phase_right;
volatile unsigned int bell_phase_left;
volatile unsigned int bell_phase_right;

// synthesized frequency of the audios
volatile float Fout_left; 
volatile float Fout_right; 
volatile float Fout_car_left;
volatile float Fout_car_right;
volatile float Fout_bell_left;
volatile float Fout_bell_right;
// phase increment to set the frequency DDS_increment = Fout*two32/Fs;
volatile unsigned int DDS_increment_left;
volatile unsigned int DDS_increment_right;
volatile unsigned int car_increment_left;
volatile unsigned int car_increment_right;
volatile unsigned int bell_increment_left;
volatile unsigned int bell_increment_right;
// global max: for intensity ratio tuning
volatile _Accum global_max_amplitude = 12;
volatile _Accum global_max_bell_amplitude = 18;
volatile _Accum global_max_car_amplitude = 180;
// max: for amplitude difference tuning
volatile _Accum max_amplitude=12;
volatile _Accum max_amplitude_left=12; 
volatile _Accum max_amplitude_right=12;
volatile _Accum max_bell_amplitude=18;
volatile _Accum max_bell_amplitude_left=18; 
volatile _Accum max_bell_amplitude_right=18;
volatile _Accum max_car_amplitude=180;
volatile _Accum max_car_amplitude_left=180; 
volatile _Accum max_car_amplitude_right=180;
// threshold values
volatile _Accum threshold_amplitude=0;
volatile _Accum bell_threshold_amplitude=0;
// waveform amplitude envelope parameters (determines the length of the audio)
volatile unsigned int attack_time_left=1000, decay_time_left=1000, sustain_time_left=3720; 
volatile unsigned int attack_time_right=1000, decay_time_right=1000, sustain_time_right=3720; 
volatile unsigned int bell_attack_time_left=2000, bell_decay_time_left=6000, bell_sustain_time_left=10000; 
volatile unsigned int bell_attack_time_right=2000, bell_decay_time_right=6000, bell_sustain_time_right=10000;
volatile unsigned int car_attack_time_left=1428, car_decay_time_left=1428, car_sustain_time_left=0; 
volatile unsigned int car_attack_time_right=1428, car_decay_time_right=1428, car_sustain_time_right=0;
// current amplitude of the audios
volatile _Accum current_amplitude_left;
volatile _Accum current_amplitude_right;
volatile _Accum current_bell_amplitude_left;
volatile _Accum current_bell_amplitude_right;
volatile _Accum current_car_amplitude_left;
volatile _Accum current_car_amplitude_right;
// amplitude change per sample during attack and decay
// no change during sustain
volatile _Accum attack_inc_left, decay_inc_left ;
volatile unsigned int note_time_left;
volatile _Accum attack_inc_right, decay_inc_right ;
volatile unsigned int note_time_right;
volatile _Accum car_attack_inc_left, car_decay_inc_left ;
volatile unsigned int car_note_time_left;
volatile _Accum car_attack_inc_right, car_decay_inc_right ;
volatile unsigned int car_note_time_right;
volatile _Accum bell_attack_inc_left, bell_decay_inc_left ;
volatile unsigned int bell_note_time_left;
volatile _Accum bell_attack_inc_right, bell_decay_inc_right ;
volatile unsigned int bell_note_time_right;
volatile _Accum bell_sustain_inc_left, bell_sustain_inc_right;

//== position control ===========================================
#define head_radius 9 
#define sound_speed 34000
volatile int map_update = 0;
// for debugging purpose
volatile int timer3_counter = 0; // bird
volatile int timer4_counter = 0; // car
volatile int timer5_counter = 0; // bell
// audio delay of the further channel
volatile double delay, bell_delay, car_delay;
volatile int timer3_delay, timer4_delay, timer5_delay;
// hardcoded sound source position
volatile int bird_x, bird_y, car_x, car_y, bell_x, bell_y;
// distance between "human" and sound sources
volatile int x_diff, bell_x_diff, car_x_diff;
volatile int y_diff, bell_y_diff, car_y_diff;
// intermediate values for spatial audio calculation
volatile double tan_value, bell_tan_value, car_tan_value;
volatile double angle_rad, bell_angle_rad, car_angle_rad;
volatile double intensity_diff, bell_intensity_diff, car_intensity_diff;
volatile double amplitude_ratio, bell_amplitude_ratio, car_amplitude_ratio;
// flag indecating whether audio source on the left or right
volatile int left, bell_left, car_left;
// counter for bell's two-note audio synthesis
volatile int bell_counter;
// hardcoded initial "human" position
static _Accum xpos=int2Accum(120), ypos=int2Accum(310);

//== Timer 2 interrupt handler ===========================================
volatile unsigned int DAC_data_A, DAC_data_B ;// audio output values
volatile SpiChannel spiChn = SPI_CHANNEL2 ;	// the SPI channel to use
volatile int spiClkDiv = 4 ; // 10 MHz max speed for port expander!!

#define float2Accum(a) ((_Accum)(a))
#define Accum2float(a) ((float)(a))
#define int2Accum(a) ((_Accum)(a))
#define Accum2int(a) ((int)(a))

void __ISR(_TIMER_2_VECTOR, ipl2) Timer2Handler(void)
{
    int junk;
    mT2ClearIntFlag();
    
    // bird audio frequenct
    Fout_left = (0.000153)*(note_time_left*note_time_left) + 2000;
    Fout_right = (0.000153)*(note_time_right*note_time_right) + 2000;
    // car audio frequenct
    int temp_left = car_note_time_left % 714;
    int temp_right = car_note_time_right % 714;
    if (temp_left < 357) Fout_car_left = 0.9014*temp_left + 0.3;
    else Fout_car_left = 1.3-0.0014*temp_left;
    if (temp_right < 357) Fout_car_right = 0.9014*temp_right + 0.3;
    else Fout_car_right = 1.3-0.0014*temp_right;
    // bell audio frequenct
    if (bell_note_time_left < 4500) Fout_bell_left = 2093;
    else if (bell_note_time_left < 9000) Fout_bell_left = 1661;
    else Fout_bell_left = 0;
    if (bell_note_time_right < 4500) Fout_bell_right = 2093;
    else if (bell_note_time_right < 9000) Fout_bell_right = 1661;
    else Fout_bell_right = 0;
    
    // direct digital synthesis calculation
    DDS_increment_left = (unsigned int)(Fout_left*DDS_constant);     
    DDS_phase_left += DDS_increment_left;
    car_increment_left = (unsigned int)(Fout_car_left*DDS_constant);
    car_phase_left += car_increment_left;      
    bell_increment_left = (unsigned int)(Fout_bell_left*DDS_constant);
    bell_phase_left += bell_increment_left;
    // DAC output: sum of all three synthesized audios
    DAC_data_A = (int)(current_amplitude_left*sine_table[DDS_phase_left>>24]) 
            + (int)(current_car_amplitude_left*sine_table[car_phase_left>>24])
            + (int)(current_bell_amplitude_left*sine_table[bell_phase_left>>24]) + 2048; 
    
    // direct digital synthesis calculation
    DDS_increment_right = (unsigned int)(Fout_right*DDS_constant);     
    DDS_phase_right += DDS_increment_right; 
    car_increment_right = (unsigned int)(Fout_car_right*DDS_constant);
    car_phase_right += car_increment_right;              
    bell_increment_right = (unsigned int)(Fout_bell_right*DDS_constant);
    bell_phase_right += bell_increment_right;
    // DAC output: sum of all three synthesized audios
    DAC_data_B = (int)(current_amplitude_right*sine_table[DDS_phase_right>>24]) 
            + (int)(current_car_amplitude_right*sine_table[car_phase_right>>24]) 
            + (int)(current_bell_amplitude_right*sine_table[bell_phase_right>>24]) + 2048; 
    
    // bird sound amplitude tuning
    if (note_time_left < (attack_time_left + decay_time_left + sustain_time_left)){
        current_amplitude_left = (note_time_left <= attack_time_left)? 
            current_amplitude_left + attack_inc_left : 
            (note_time_left <= attack_time_left + sustain_time_left)? current_amplitude_left:
                current_amplitude_left - decay_inc_left;
    } else { 
        current_amplitude_left = threshold_amplitude; // no sound
    }
    if (note_time_right < (attack_time_right + decay_time_right + sustain_time_right)){
        current_amplitude_right = (note_time_right <= attack_time_right)? 
            current_amplitude_right + attack_inc_right : 
            (note_time_right <= attack_time_right + sustain_time_right)? current_amplitude_right:
                current_amplitude_right - decay_inc_right;
    } else { 
        current_amplitude_right = threshold_amplitude; // no sound
    }
    
    // bell sound amplitude tuning
    if (bell_note_time_left < (bell_attack_time_left + bell_decay_time_left + bell_sustain_time_left)){
        current_bell_amplitude_left = (bell_note_time_left <= bell_attack_time_left)? 
            current_bell_amplitude_left + bell_attack_inc_left : 
            (bell_note_time_left <= bell_attack_time_left + bell_sustain_time_left)? current_bell_amplitude_left:
                current_bell_amplitude_left - bell_decay_inc_left;
    } else { 
        current_bell_amplitude_left = bell_threshold_amplitude; // no sound
    }
    if (bell_note_time_right < (bell_attack_time_right + bell_decay_time_right + bell_sustain_time_right)){
        current_bell_amplitude_right = (bell_note_time_right <= bell_attack_time_right)? 
            current_bell_amplitude_right + bell_attack_inc_right : 
            (bell_note_time_right <= bell_attack_time_right + bell_sustain_time_right)? current_bell_amplitude_right:
                current_bell_amplitude_right - bell_decay_inc_right;
    } else { 
        current_bell_amplitude_right = bell_threshold_amplitude; // no sound
    }
    
    // car sound amplitude tuning
    if (car_note_time_left < (car_attack_time_left + car_decay_time_left + car_sustain_time_left)){
        current_car_amplitude_left = (car_note_time_left <= car_attack_time_left)? 
            current_car_amplitude_left + car_attack_inc_left : 
            (car_note_time_left <= car_attack_time_left + car_sustain_time_left)? current_car_amplitude_left:
                current_car_amplitude_left - car_decay_inc_left;
    } else { 
        current_car_amplitude_left = threshold_amplitude; // no sound
    }
    
    if (car_note_time_right < (car_attack_time_right + car_decay_time_right + car_sustain_time_right)){
        current_car_amplitude_right = (car_note_time_right <= car_attack_time_right)? 
            current_car_amplitude_right + car_attack_inc_right : 
            (car_note_time_right <= car_attack_time_right + car_sustain_time_right)? current_car_amplitude_right:
                current_car_amplitude_right - car_decay_inc_right;
    } else { 
        current_car_amplitude_right = threshold_amplitude; // no sound
    }

    while (TxBufFullSPI2()); // test for ready
    SPI_Mode16();            // reset spi mode to avoid conflict with expander
    mPORTBClearBits(BIT_4);  // DAC-A CS low to start transaction
    WriteSPI2(DAC_config_chan_A | (DAC_data_A & 0xfff) );  // write to spi2

    while (SPI2STATbits.SPIBUSY); // wait for end of transaction
    junk = ReadSPI2();            // MUST read to clear buffer for port expander elsewhere in code
    mPORTBSetBits(BIT_4);         // CS high to end transaction

    mPORTBClearBits(BIT_4);       // DAC-B CS low to start transaction
    WriteSPI2(DAC_config_chan_B | (DAC_data_B & 0xfff) );  // write to spi2

    // while waiting for SPI transaction, check audio counters
    // move to the next sound samplie; if finished one iteration, start replaying
    if (note_time_left < 100000) note_time_left++;
    else note_time_left = 0;
    if (note_time_right < 100000) note_time_right++;
    else note_time_right = 0;
    if (car_note_time_left < 2856) car_note_time_left++;
    else car_note_time_left = 0;
    if (car_note_time_right < 2856) car_note_time_right++;
    else car_note_time_right = 0;
    if (bell_note_time_left < 70000) bell_note_time_left++;
    else bell_note_time_left = 0;
    if (bell_note_time_right < 70000) bell_note_time_right++;
    else bell_note_time_right = 0;
    
    while (SPI2STATbits.SPIBUSY); // wait for end of transaction
    junk = ReadSPI2();            // MUST read to clear buffer for port expander elsewhere in code
    mPORTBSetBits(BIT_4); // CS high - end transaction
}

// ISR for bird sound spatial audio delay implementation
void __ISR(_TIMER_3_VECTOR, ipl1) Timer3Handler(void)
{
    mT3ClearIntFlag();
    timer3_counter++;
    if (left == 1) {
        // sound source on the right
        // perform spatial audio amplitude ratio tuning
        // calculate the amplitude change per sample during attack and decay
        max_amplitude_left = (_Accum)((double)(max_amplitude - threshold_amplitude) *amplitude_ratio)+threshold_amplitude;
        attack_inc_left = (max_amplitude_left-threshold_amplitude)/(_Accum)attack_time_left;
        decay_inc_left = (max_amplitude_left-threshold_amplitude)/(_Accum)decay_time_left;
        // set note time to 0 to enable audio
        note_time_left = 0;
    } else {
        // sound source on the left
        // perform spatial audio amplitude ratio tuning
        // calculate the amplitude change per sample during attack and decay
        max_amplitude_right = (_Accum)((double)(max_amplitude - threshold_amplitude) *amplitude_ratio)+threshold_amplitude;
        attack_inc_right = (max_amplitude_right-threshold_amplitude)/(_Accum)attack_time_right;
        decay_inc_right = (max_amplitude_right-threshold_amplitude)/(_Accum)decay_time_right;
        // set note time to 0 to enable audio
        note_time_right = 0;
    }
    CloseTimer3();
}

// ISR for car sound spatial audio delay implementation
void __ISR(_TIMER_4_VECTOR, ipl1) Timer4Handler(void)
{
    mT4ClearIntFlag();
    timer4_counter++;
    if (car_left == 1) {
        // sound source on the right
        // perform spatial audio amplitude ratio tuning
        // calculate the amplitude change per sample during attack and decay
        max_car_amplitude_left = (_Accum)((double)(max_car_amplitude - threshold_amplitude) *car_amplitude_ratio)+threshold_amplitude;
        car_attack_inc_left = (max_car_amplitude_left-threshold_amplitude)/(_Accum)car_attack_time_left;
        car_decay_inc_left = (max_car_amplitude_left-threshold_amplitude)/(_Accum)car_decay_time_left;
        // set note time to 0 to enable audio
        car_note_time_left = 0;
    } else {
        // sound source on the left
        // perform spatial audio amplitude ratio tuning
        // calculate the amplitude change per sample during attack and decay
        max_car_amplitude_right = (_Accum)((double)(max_car_amplitude - threshold_amplitude) * car_amplitude_ratio)+threshold_amplitude;
        car_attack_inc_right = (max_car_amplitude_right-threshold_amplitude)/(_Accum)car_attack_time_right;
        car_decay_inc_right = (max_car_amplitude_right-threshold_amplitude)/(_Accum)car_decay_time_right;
        // set note time to 0 to enable audio
        car_note_time_right = 0;
    }
    CloseTimer4();
}

// ISR for bell sound spatial audio delay implementation
void __ISR(_TIMER_5_VECTOR, ipl1) Timer5Handler(void)
{
    mT5ClearIntFlag();
    timer5_counter++;
    if (bell_left == 1) {
        // sound source on the right
        // perform spatial audio amplitude ratio tuning
        // calculate the amplitude change per sample during attack and decay
        max_bell_amplitude_left = (_Accum)((double)(max_bell_amplitude - bell_threshold_amplitude) * bell_amplitude_ratio)+bell_threshold_amplitude;
        bell_attack_inc_left = (max_bell_amplitude_left-bell_threshold_amplitude)/(_Accum)bell_attack_time_left;
        bell_decay_inc_left = (max_bell_amplitude_left-bell_threshold_amplitude)/(_Accum)bell_decay_time_left;
        // set note time to 0 to enable audio
        bell_note_time_left = 0;
    } else {
        // sound source on the left
        // perform spatial audio amplitude ratio tuning
        // calculate the amplitude change per sample during attack and decay
        max_bell_amplitude_right = (_Accum)((double)(max_bell_amplitude - bell_threshold_amplitude) * bell_amplitude_ratio)+bell_threshold_amplitude;
        bell_attack_inc_right = (max_bell_amplitude_right-bell_threshold_amplitude)/(_Accum)bell_attack_time_right;
        bell_decay_inc_right = (max_bell_amplitude_right-bell_threshold_amplitude)/(_Accum)bell_decay_time_right;
        // set note time to 0 to enable audio
        bell_note_time_right = 0;
    }
    CloseTimer5();
}

// === TFT map  ======================================================
void collegetown_map(void) {
    tft_fillRect(80, 0, 80, 320, ILI9340_BLACK);
    tft_fillRect(0, 120, 240, 80, ILI9340_BLACK);
    int ix, iy;
    // cross walk
    for (ix = 82; ix < 160; ix = ix + 10) {
        tft_fillRect(ix, 100, 5, 20, ILI9340_WHITE);
        tft_fillRect(ix, 200, 5, 20, ILI9340_WHITE);
    }
    for (iy = 122; iy < 200; iy = iy + 10) {
        tft_fillRect(60, iy, 20, 5, ILI9340_WHITE);
        tft_fillRect(160, iy, 20, 5, ILI9340_WHITE);
    }
    // traffic light
    tft_fillCircle(120, 112, 8, ILI9340_GREEN);
    tft_fillCircle(168, 160, 8, ILI9340_RED);
    // construction site
    tft_fillTriangle(40, 140, 40, 180, 75, 160, ILI9340_ORANGE);
    tft_fillRect(43, 158, 4, 4, ILI9340_BLACK);
    tft_fillRect(50, 158, 18, 4, ILI9340_BLACK);
    // oishii bowl
    tft_fillRect(165, 216, 5, 14, ILI9340_OISHII);
    tft_fillCircle(183, 222, 15, ILI9340_OISHII);
    tft_fillRect(183, 200, 16, 250, ILI9340_GRAY);
    tft_fillCircle(183, 222, 8, ILI9340_WHITE);
    tft_fillRect(179, 214, 4, 18, ILI9340_OISHII);
    tft_fillRect(175, 216, 4, 14, ILI9340_OISHII);
    // car
    tft_fillCircle(130, 25, 20, ILI9340_RED);
    tft_fillRect(110, 5, 20, 50, ILI9340_BLACK);
    tft_fillRect(144, 5, 10, 50, ILI9340_BLACK);
    tft_fillCircle(142, 25, 12, ILI9340_GRAY);
    tft_fillRect(130, 10, 14, 30, ILI9340_RED);
    tft_fillCircle(130, 15, 3, ILI9340_GRAY);
    tft_fillCircle(130, 35, 3, ILI9340_GRAY);
    // middle line
    for (iy = 0; iy < 100; iy = iy + 10) {
        tft_fillRect(119, iy, 2, 5, ILI9340_WHITE);
    }
    for (iy = 225; iy < 320; iy = iy + 10) {
        tft_fillRect(119, iy, 2, 5, ILI9340_WHITE);
    }
    for (ix = 0; ix < 60; ix = ix + 10) {
        tft_fillRect(ix, 159, 5, 2, ILI9340_WHITE);
    }
    for (ix = 185; ix < 240; ix = ix + 10) {
        tft_fillRect(ix, 159, 5, 2, ILI9340_WHITE);
    }
    // construction site
    tft_fillTriangle(40, 140, 40, 180, 75, 160, ILI9340_ORANGE);
    tft_fillRect(43, 158, 4, 4, ILI9340_BLACK);
    tft_fillRect(50, 158, 18, 4, ILI9340_BLACK);
    // bird
    tft_fillTriangle(61, 109, 67, 108, 64, 116, ILI9340_BROWN);
    tft_fillCircle(64, 102, 7, ILI9340_YELLOW);
    tft_fillCircle(65, 101, 2, ILI9340_BLACK);
}

void fix_map(void) {
    int ix, iy;
    // cross walk
    for (ix = 82; ix < 160; ix = ix + 10) {
        tft_fillRect(ix, 100, 5, 20, ILI9340_WHITE);
        tft_fillRect(ix, 200, 5, 20, ILI9340_WHITE);
    }
    tft_fillCircle(120, 112, 8, ILI9340_GREEN);
    // middle line
    for (iy = 0; iy < 100; iy = iy + 10) {
        tft_fillRect(119, iy, 2, 5, ILI9340_WHITE);
    }
    for (iy = 225; iy < 320; iy = iy + 10) {
        tft_fillRect(119, iy, 2, 5, ILI9340_WHITE);
    }
}

// === thread structures ============================================
// thread control structs
static struct pt pt_timer, pt_joystick;

// system 1 second interval tick
int sys_time_seconds;

// === Timer Thread =================================================
// update a 1 second tick counter
static PT_THREAD (protothread_timer(struct pt *pt))
{
    PT_BEGIN(pt);
      while(1) {
        // yield time 500ms
        PT_YIELD_TIME_msec(500) ;
        sys_time_seconds++ ;
        //******** Joystick + Map Stuff ****************** //
        static int adc11_x, adc5_y;
        // read ADC value
        adc5_y = ReadADC10(0);   
        adc11_x = ReadADC10(1);   
        tft_fillCircle(Accum2int(xpos), Accum2int(ypos), 4, ILI9340_BLACK); 
        // determines if there is movement
        if (adc5_y < 300 && adc5_y >= 0 && ypos > int2Accum(10)) {
            ypos -= 10;
            map_update = 1;
            // avoid the car region
            if (xpos < int2Accum(160) && xpos > int2Accum(120) && ypos < int2Accum(50)) {
                ypos += 10;
            }
        }
        if (adc5_y > 600 && adc5_y <= 1023 && ypos < int2Accum(310)) {
            ypos += 10;
            map_update = 1;
        }
        if (adc11_x < 300 && adc11_x >= 0 && xpos > int2Accum(90)) {
            xpos -= 10; 
            map_update = 1;
        }
        if (adc11_x > 600 && adc11_x <= 1023 && xpos < int2Accum(150)) {
            xpos += 10;
            map_update = 1;
            // avoid the car region
            if (xpos < int2Accum(160) && xpos > int2Accum(120) && ypos < int2Accum(50)) {
                xpos -= 10;
            }
        }
        // update map and close Timer2 (audio output)
        if (map_update == 1) {
            CloseTimer2();
            fix_map();
            map_update = 0;
        }
        tft_fillCircle(Accum2int(xpos), Accum2int(ypos), 4, ILI9340_GREEN);
        //******** Joystick + Map Stuff ****************** //
        
        //******** spatial audio ****************** //
        // if joystick button pressed, update spatial audio calculation
        if (!mPORTBReadBits(BIT_7)) {
            // bird spatial audio calibration
            x_diff = bird_x-Accum2int(xpos);
            y_diff = bird_y-Accum2int(ypos);
            tan_value = (double)(abs(x_diff))/(double)(abs(y_diff));
            angle_rad = atan(tan_value);
            // amplitude ratio & delay calculation, used in timer 3/4/5 interrupt for the further channel
            amplitude_ratio = cos(angle_rad);
            delay = head_radius*(angle_rad + sin(angle_rad))/sound_speed;
            timer3_delay = (int)(40000000 * delay);
            // intensity decay tuning -- customized for each audio source
            intensity_diff = (10 * log(sqrt((x_diff*x_diff)+(y_diff*y_diff))/6) / log(10)) - 2;
            max_amplitude = global_max_amplitude - (_Accum)(intensity_diff);
            if (max_amplitude < 0) max_amplitude = 0;
            else if (max_amplitude > 12) max_amplitude = 12;
            if (x_diff > 0) {
                // sound source on the right
                // perform spatial audio amplitude ratio tuning
                // calculate the amplitude change per sample during attack and decay
                left = 1;
                max_amplitude_right = max_amplitude;
                attack_inc_right = (max_amplitude_right-threshold_amplitude)/(_Accum)attack_time_right;
                decay_inc_right = (max_amplitude_right-threshold_amplitude)/(_Accum)decay_time_right;
                // set note time to 0 to enable audio; the further channel is enabled after the delay
                note_time_right = 0;
            } else {
                // sound source on the left
                // perform spatial audio amplitude ratio tuning
                // calculate the amplitude change per sample during attack and decay
                left = 0;
                max_amplitude_left = max_amplitude;
                attack_inc_left = (max_amplitude_left-threshold_amplitude)/(_Accum)attack_time_left;
                decay_inc_left = (max_amplitude_left-threshold_amplitude)/(_Accum)decay_time_left;
                // set note time to 0 to enable audio; the further channel is enabled after the delay
                note_time_left = 0;
            }
             
            // car spatial audio calibration
            car_x_diff = car_x-Accum2int(xpos);
            car_y_diff = car_y-Accum2int(ypos);
            car_tan_value = (double)(abs(car_x_diff))/(double)(abs(car_y_diff));
            car_angle_rad = atan(car_tan_value);
            // amplitude ratio & delay calculation, used in timer 3/4/5 interrupt for the further channel
            car_amplitude_ratio = cos(car_angle_rad);
            car_delay = head_radius*(car_angle_rad + sin(car_angle_rad))/sound_speed;
            timer4_delay = (int)(40000000 * car_delay);
            // intensity decay tuning -- customized for each audio source
            car_intensity_diff = (150 * log(sqrt((car_x_diff*car_x_diff)+(car_y_diff*car_y_diff))/20) / log(10));
            max_car_amplitude = global_max_car_amplitude - (_Accum)(car_intensity_diff);
            if (max_car_amplitude < 0) max_car_amplitude = 0;
            else if (max_car_amplitude > 180) max_car_amplitude = 180;
            if (car_x_diff > 0) {
                // sound source on the right
                // perform spatial audio amplitude ratio tuning
                // calculate the amplitude change per sample during attack and decay
                car_left = 1;
                max_car_amplitude_right = max_car_amplitude;
                car_attack_inc_right = (max_car_amplitude_right-threshold_amplitude)/(_Accum)car_attack_time_right;
                car_decay_inc_right = (max_car_amplitude_right-threshold_amplitude)/(_Accum)car_decay_time_right;
                // set note time to 0 to enable audio; the further channel is enabled after the delay
                car_note_time_right = 0;
            } else {
                // sound source on the left
                // perform spatial audio amplitude ratio tuning
                // calculate the amplitude change per sample during attack and decay
                car_left = 0;
                max_car_amplitude_left = max_car_amplitude;
                car_attack_inc_left = (max_car_amplitude_left-threshold_amplitude)/(_Accum)car_attack_time_left ;
                car_decay_inc_left = (max_car_amplitude_left-threshold_amplitude)/(_Accum)car_decay_time_left ;
                // set note time to 0 to enable audio; the further channel is enabled after the delay
                car_note_time_left = 0;
            }
            
            // bell spatial audio calibration
            bell_x_diff = bell_x-Accum2int(xpos);
            bell_y_diff = bell_y-Accum2int(ypos);
            bell_tan_value = (double)(abs(bell_x_diff))/(double)(abs(bell_y_diff));
            bell_angle_rad = atan(bell_tan_value);
            // amplitude ratio & delay calculation, used in timer 3/4/5 interrupt for the further channel
            bell_amplitude_ratio = cos(bell_angle_rad);
            bell_delay = head_radius*(bell_angle_rad + sin(bell_angle_rad))/sound_speed;
            timer5_delay = (int)(40000000 * bell_delay);
            // intensity decay tuning -- customized for each audio source
            bell_intensity_diff = (15 * log(sqrt((bell_x_diff*bell_x_diff)+(bell_y_diff*bell_y_diff))/6) / log(10)) - 1;
            max_bell_amplitude = global_max_bell_amplitude - (_Accum)(bell_intensity_diff);
            if (max_bell_amplitude < 0) max_bell_amplitude = 0;
            else if (max_bell_amplitude > 18) max_bell_amplitude = 18;
            if (bell_x_diff > 0) {
                // sound source on the right
                // perform spatial audio amplitude ratio tuning
                // calculate the amplitude change per sample during attack and decay
                bell_left = 1;
                max_bell_amplitude_right = max_bell_amplitude;
                bell_attack_inc_right = (max_bell_amplitude_right-bell_threshold_amplitude)/(_Accum)bell_attack_time_right;
                bell_decay_inc_right = (max_bell_amplitude_right-bell_threshold_amplitude)/(_Accum)bell_decay_time_right;
                // set note time to 0 to enable audio; the further channel is enabled after the delay
                bell_note_time_right = 0;
            } else {
                // sound source on the left
                // perform spatial audio amplitude ratio tuning
                // calculate the amplitude change per sample during attack and decay
                bell_left = 0;
                max_bell_amplitude_left = max_bell_amplitude;
                bell_attack_inc_left = (max_bell_amplitude_left-bell_threshold_amplitude)/(_Accum)bell_attack_time_left;
                bell_decay_inc_left = (max_bell_amplitude_left-bell_threshold_amplitude)/(_Accum)bell_decay_time_left;
                // set note time to 0 to enable audio; the further channel is enabled after the delay
                bell_note_time_left = 0;
            }
            
            // timer interrupt
            // Set up timer2 on for DAC
            // at 40 MHz PB clock; timer value = 40,000,000/Fs
            OpenTimer2(T2_ON | T2_SOURCE_INT | T2_PS_1_1, 2667);
            // set up the timer interrupt with a priority of 2
            ConfigIntTimer2(T2_INT_ON | T2_INT_PRIOR_2);
            mT2ClearIntFlag(); // and clear the interrupt flag
            // Timer 3 Setup -- bird audio delay tuning
            OpenTimer3(T3_ON | T3_SOURCE_INT | T3_PS_1_1, timer3_delay);
            // set up the timer interrupt with a priority of 1
            ConfigIntTimer3(T3_INT_ON | T3_INT_PRIOR_1);
            mT3ClearIntFlag(); // and clear the interrupt flag
            // Timer 4 Setup -- car audio delay tuning
            OpenTimer4(T4_ON | T4_SOURCE_INT | T4_PS_1_1, timer4_delay);
            // set up the timer interrupt with a priority of 1
            ConfigIntTimer4(T4_INT_ON | T4_INT_PRIOR_1);
            mT4ClearIntFlag(); // and clear the interrupt flag
            // Timer 5 Setup -- bell audio delay tuning
            OpenTimer5(T5_ON | T5_SOURCE_INT | T5_PS_1_1, timer5_delay);
            // set up the timer interrupt with a priority of 1
            ConfigIntTimer5(T5_INT_ON | T5_INT_PRIOR_1);
            mT5ClearIntFlag(); // and clear the interrupt flag
        }
        //******** spatial audio ****************** //

        // !!!! NEVER exit while !!!!
      } // END WHILE(1)
  PT_END(pt);
} // timer thread


// === Main  ======================================================
void main(void) {
 //SYSTEMConfigPerformance(PBCLK);
  
    ANSELA = 0; ANSELB = 0;  
    // disable audio after reset
    CloseTimer2();
    CloseTimer3();
    CloseTimer4();
    CloseTimer5();

    // SCK2 is pin 26 
    // SDO2 (MOSI) is in PPS output group 2, could be connected to RB5 which is pin 14
    PPSOutput(2, RPB5, SDO2);

    // control CS for DAC
    mPORTBSetPinsDigitalOut(BIT_4);
    mPORTBSetBits(BIT_4);

    // open SPI channel2 for DAC audio output
    // divide Fpb by 2, configure the I/O ports. Not using SS in this example
    // 16 bit transfer CKP=1 CKE=1
    // possibles SPI_OPEN_CKP_HIGH;   SPI_OPEN_SMP_END;  SPI_OPEN_CKE_REV
    // For any given peripherial, you will need to match these
    // clk divider set to 4 for 10 MHz
    SpiChnOpen(SPI_CHANNEL2, SPI_OPEN_ON | SPI_OPEN_MODE16 | SPI_OPEN_MSTEN | SPI_OPEN_CKE_REV , 4);
    
   // build the sine lookup table
   // scaled to produce values between 0 and 4096
   int i;
   for (i = 0; i < sine_table_size; i++){
        sine_table[i] = (_Accum)(sin((float)i*6.283/(float)sine_table_size));
    }
    
    // init the display
    // NOTE that this init assumes SPI channel 1 connections
    tft_init_hw();
    tft_begin();
    tft_fillScreen(ILI9340_GRAY);
    tft_setRotation(2); 
    
    // the ADC
    // configure and enable the ADC
	CloseADC10();	// ensure the ADC is off before setting the configuration

	// define setup parameters for OpenADC10
	// Turn module on | ouput in integer | trigger mode auto | enable autosample
    // ADC_CLK_AUTO -- Internal counter ends sampling and starts conversion (Auto convert)
    // ADC_AUTO_SAMPLING_ON -- Sampling begins immediately after last conversion completes; SAMP bit is automatically set
    // ADC_AUTO_SAMPLING_OFF -- Sampling begins with AcquireADC10();
    #define PARAM1  ADC_FORMAT_INTG16 | ADC_CLK_AUTO | ADC_AUTO_SAMPLING_ON //

	// define setup parameters for OpenADC10
	// ADC ref external  | disable offset test | disable scan mode | do 1 sample | use single buf | alternate mode off
	#define PARAM2  ADC_VREF_AVDD_AVSS | ADC_OFFSET_CAL_DISABLE | ADC_SCAN_ON | ADC_SAMPLES_PER_INT_2 | ADC_ALT_BUF_OFF | ADC_ALT_INPUT_OFF
        //
	// Define setup parameters for OpenADC10
    // use peripherial bus clock | set sample time | set ADC clock divider
    // ADC_CONV_CLK_Tcy2 means divide CLK_PB by 2 (max speed)
    // ADC_SAMPLE_TIME_5 seems to work with a source resistance < 1kohm
    #define PARAM3 ADC_CONV_CLK_PB | ADC_SAMPLE_TIME_15 | ADC_CONV_CLK_Tcy 

	// define setup parameters for OpenADC10
	// set AN11 and  as analog inputs
	#define PARAM4	ENABLE_AN11_ANA | ENABLE_AN5_ANA // 

	// define setup parameters for OpenADC10
    // DO not skip the channels you want to scan
    // do not specify channels  5 and 11
	#define PARAM5	SKIP_SCAN_AN0 | SKIP_SCAN_AN1 | SKIP_SCAN_AN2 | SKIP_SCAN_AN3 | SKIP_SCAN_AN4 | SKIP_SCAN_AN6 | SKIP_SCAN_AN7 | SKIP_SCAN_AN8 | SKIP_SCAN_AN9 | SKIP_SCAN_AN10 | SKIP_SCAN_AN12 | SKIP_SCAN_AN13 | SKIP_SCAN_AN14 | SKIP_SCAN_AN15

	// use ground as neg ref for A 
    // actual channel number is specified by the scan list
    SetChanADC10( ADC_CH0_NEG_SAMPLEA_NVREF); // 
	OpenADC10( PARAM1, PARAM2, PARAM3, PARAM4, PARAM5 ); // configure ADC using the parameters defined above

	EnableADC10(); // Enable the ADC
  
    // hardcoded sound source positions
    bird_x = 80;
    bird_y = 120;
    car_x = 142;
    car_y = 25;
    bell_x = 183;
    bell_y = 221;
    // initialize the maps
    collegetown_map();
    
    // === setup system wide interrupts  ========
    INTEnableSystemMultiVectoredInt();
    
    // === config threads ==========
    // turns OFF UART support and debugger pin, unless defines are set
    PT_setup();

    // init the threads
    PT_INIT(&pt_timer);
    
    // round-robin scheduler for threads
    while (1){
        PT_SCHEDULE(protothread_timer(&pt_timer));
    }
} // main

// === end  ======================================================
