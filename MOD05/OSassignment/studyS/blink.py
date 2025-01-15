from time import sleep
from gpiozero import LED
# Set up the LED on GPIO pin 17
led = LED(17)

# Blink the LED in a loop
while True:
    led.toggle()    # on -> off ; off-> on
    sleep(0.5)
