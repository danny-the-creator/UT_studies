import math
import neca
from neca.events import *
from neca.generators import generate_data
from neca.generators import print_object
import re
import json
from urllib.request import urlopen
from flask import Flask, request
from neca.settings import app, socket


list= ["hagelbui", "sneeuwstorm", "sneeuw", "weeralarm", "onweer", "tsunami", "nood", "bliksem", "storm", "donder", "ramp", "overstroming", "rood", "tornado", "orkaan", "heftig", "gevaarlijk", "trauma", "slachtoffers", "hagel", "hagelt", "hagelen", "hevig", "pas op", "oppassen", "opgepast", "opgelet", "waarschuwing", "alert", "extreem", "extreme"]
# Generate and emit tweets from a data file
generate_data('weer.txt', time_scale=10000, event_name='init') 
# Print the tweet object to the console

def your_city():
    url = r"https://ipinfo.io/json"
    response = urlopen(url)
    return json.load(response)['city']

# GLOBAL
Name = your_city()
# Name = 'Amsterdam'

coords = {"Amsterdam": [ 4.895168,52.370216],
          "Groningen": [ 6.566502,53.219383],
          "Den Bosch":[  5.303675,51.697816],
          "Leiden":[  4.497010,52.160114],
          "Zwolle":[ 6.092654,52.514738],
          "Amersfoort":[5.387827,52.156111],
          "Almere":[5.264702,52.350785],
          "Leeuwarden":[ 5.799913, 53.201233,],
          "Den Helder":[ 4.761484,52.958148],
          "Almelo":[  6.662179,52.356428],
          "Harderwijk":[ 5.620016,52.341242],
          "Gorinchem":[4.974361, 51.829827],
          "Meppel":[6.194106,52.694432],
          "Rotterdam":[ 4.479170,51.92250],
          "Maastricht":[ 5.688672,50.850340],
          "Haarlem":[ 4.646219,52.387388],
          "Eindhoven":[  5.469722,51.441642],
          "Nijmegen":[ 5.853370, 51.842509,],
          "Enschede":[6.893662,52.221537],
          "Alkmaar":[4.750606,52.631418],
          "Deventer":[6.163490,52.255717],
          "Hoorn":[5.059707,52.642537],
          "Heerlen":[ 5.978514,50.884548],
          "Kampen":[5.907286, 52.558883],
          "Enkhuizen":[ 5.292453,52.703662],
          "Hengelo":[  6.794490,52.265224],
          "Geertruidenberg":[4.863752,51.703276],
          "The Hague":[ 4.300700,52.070498],
          "Den Haag":[4.300700, 52.070498],
          "Breda":[4.754483, 51.590724],
          "Delft":[4.357067, 52.011576],
          "Utrecht":[5.121420, 52.090737],
          "Gouda":[4.710139, 52.011577],
          "Arnhem":[5.898730, 51.985103],
          "Wageningen":[5.666632, 51.966961],
          "Dordrecht":[4.695738, 51.811728],
          "Assen":[6.564726, 52.992052],
          "Harlingen":[5.414111, 53.173058],
          "Goes":[3.888981, 51.504132],
          "Medemblik":[5.100043, 52.772650],
          "Helmond":[5.661965, 51.479489],
          "Zaanstad":[4.822226, 52.454216],
          "Roermond":[6.008913, 51.194180],
          "Elburg":[5.833797, 52.448141],
          "Culemborg":[5.220112, 51.955044],
          "Hilversum":[5.170726,52.230416],
          "Schiedam":[4.393179,51.919133],
          "Maassluis":[4.257836,51.922307],
          "Zutphen":[6.196217,52.138563]
          }


def distance(x, y):
    dist = math.sqrt((x[0]-y[0])**2 + (x[1]-y[1])**2)
    return dist

@app.route("/api/myForm", methods=["POST"])
def form():
    global Name
    Name = request.json['Name']
    print('--------------------')
    print(Name)
    return "ok", 200

@event("init")
def init(context, tweet):
    fire_global("coord_tweet", tweet, delay=2)
    fire_global("popular_tweet", tweet, delay=2)
    fire_global("danger_trig", tweet, delay=2)
    
@event("coord_tweet")
def tweet_event(context, tweet) :
    print(Name)
    location = coords.get(Name)
    if location == None:
        location = coords['Enschede']
    print(location)
    # print(tweet["coordinates"]["coordinates"])                          # Just for check
    # print(distance (tweet["coordinates"]["coordinates"], coords[Name])) # Just for check
    # print('--------------------')                                       # Just for check
    if (distance (tweet["coordinates"]["coordinates"], location) < 1) and ((tweet["user"]["name"]) != "WS kapel-avezaath"): # max distance between tweet and user's location
        emit("tweet_stream", tweet) 
        # print(tweet["coordinates"]["coordinates"]) #shows the coordinates DO NOT DELETEEEEEE!!!!!
        # print_object(tweet)#shows the routes to the information about the tweets DO NOT DELETEEEEEE!!!!!!!

@event("danger_trig")
def trigger(context,tweet):
    test_string = tweet["text"]
    pres=test_string.split()
    res = re.findall(r'\w+', test_string)
    # print (str(res))
    if (tweet["user"]["name"]) == "WS kapel-avezaath":
        temp = float(str(pres[1]).replace(',','.')[:-2])
        emit("linechart", {
        "action": "add",
        "value": [tweet["created_at"] ,temp]
        })

    j=0
    while j<len(res):
        i=0
        while i<len(list):
            if list[i]==res[j]:
                fire_global("danger", tweet, delay=5)
                i=len(list)
                j=len(res)
            else:
                i=i+1
        j=j+1

@event("danger")
def tweet2_event(context,tweet):
    if tweet["user"]["name"] != "WS kapel-avezaath":
        emit("danger_stream", tweet) 


top_l = {'1st': -1,
        '2nd': -1,
        '3rd': -1}
top_t = {'1st': None,
        '2nd': None,
        '3rd': None}

@event("popular_tweet")
def tweet_event(context, tweet):
    # print(top_l["1st"])
    # print(top_l["2nd"])
    # print(top_l["3rd"])
    # print()
    # print(tweet['user']['name'], tweet['user']['followers_count'])
    # print('-------------------------------------------------------')
    if tweet['user']['followers_count'] > top_l["1st"]:
        top_l['3rd'] = top_l["2nd"]
        top_l["2nd"]= top_l["1st"]
        top_l["1st"] = tweet['user']['followers_count']

        top_t['3rd'] = top_t["2nd"]
        top_t["2nd"]= top_t["1st"]
        top_t['1st'] = tweet

        emit("tweet_top", top_t["3rd"])
        emit("tweet_top", top_t["2nd"])
        emit("tweet_top", top_t["1st"])
    elif tweet['user']['followers_count'] > top_l["2nd"]:
        top_l["3rd"] = top_l["2nd"]
        top_l["2nd"] = tweet['user']['followers_count']

        top_t["3rd"] = top_t["2nd"]
        top_t['2nd'] = tweet
        emit("tweet_top", top_t["3rd"])
        emit("tweet_top", top_t["2nd"])
        emit("tweet_top", top_t["1st"])
    elif tweet['user']['followers_count'] > top_l["3rd"]:
        top_l["3rd"] = tweet['user']['followers_count']
        top_t["3rd"] = tweet
        emit("tweet_top", top_t["3rd"])
        emit("tweet_top", top_t["2nd"])
        emit("tweet_top", top_t["1st"])
    # else:
    #     emit("tweet_top", top_t["3rd"])
    #     emit("tweet_top", top_t["2nd"])
    #     emit("tweet_top", top_t["1st"])


# print_object("tweet")
neca.start()

# print (top_t)