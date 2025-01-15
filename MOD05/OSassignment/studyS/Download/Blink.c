/* Make the LED connected to GPIO pin 17 blink at a 1 second interval */

#include <wiringPi.h>
#define N 10

int main(int argc, char * argv[]){
   int i;
    wiringPiSetup();
    pinMode(0, OUTPUT);
    for(i=0; i<N; i++) {
        digitalWrite(0, HIGH); delay(500);
        digitalWrite(0, LOW); delay(500);
    }
    return 0 ;
}
