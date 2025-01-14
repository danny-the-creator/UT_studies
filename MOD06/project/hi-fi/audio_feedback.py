from gtts import gTTS
import pyglet as pg
import os
from time import sleep

PATH = r'D:\studies\MOD06\project\hi-fi\trash\DoNotTouch\{}'
VOLUME = 0.05
MESSAGES = {
    # Real time feedback
    '1': "Hands too close together! Your hands should be 5 cm wider than shoulder-width apart.",
    '2': "Hands too far apart! Your hands should be 5 cm wider than shoulder-width apart.",
    '3': "Your wrists are in front! Put them back",
    '4': "Flared elbows!  your elbows stay ± 45° from your back",
    '5': "Wrong hips position! Lift them up higher",
    '6': "Wrong hips position! Lower them down",
    '7': "Incomplete reps! You should go all the way down, not just half-way",
    '8': "Shoulders Rolling Around! Keep them aligned directly over your wrists",
    '9': "You pump out reps too fast!  Focus and do it slower!",
    '10': "Improper neck alignment! Your neck should be in neutral alignment with your spine",
    '11': "Your lower back is arching! Keep your back lower.",
    '12': "Your lower back is sagging! Keep your back higher.",
    '13': "Wrong feet position! Keep your feet together!",
    # Step by step
    '14': "Put your hands 5cm wider than shoulder-width apart.",
    '15': "Align your wrists with your shoulders",
    '16': "Point your fingers between forward and slightly outward.",
    '17': "Engage your core and maintain a straight line from your head to heels.",
    '18': "Put your feet close together.",
    '19': "Lower your body by bending your elbows while keeping them close to your torso.",
    '20': "Lower yourself until your chest is about an inch above the ground.",
    '21': "Push through your palms to extend your elbows.",
    '22': "Return to the starting position by extending your arms without locking your elbow"

}

def speak(text, language="en"):
    filename = 'voice_message_playing.mp3'
    tts = gTTS(text=text, lang=language)
    tts.save(PATH.format(filename))
    music = pg.media.load(PATH.format(filename), streaming=False)
    music.play()
    sleep(music.duration)
    sleep(0.3)
    try:
        os.remove(PATH.format(filename))
    except FileNotFoundError:
        pass
    # pg.mixer.music.set_volume(volume)


if __name__ == '__main__':
    # speak("something")
    while True:
        command = input("Choose number of a phrase: ")
        if command == '-1':
            break
        if command not in MESSAGES.keys():
            print("Incorrect number!")
            continue
        speak(MESSAGES[command])