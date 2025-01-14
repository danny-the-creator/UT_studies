p.
q.
r.
s.
a :- b,c.
b :- p,q.
c :- r,s.
/*
 Ex #1
1. abpqcrs
2.
*/


person(alisha).
person(frank).
person(eve).
person(alex).
corona_symptom(cold).
corona_symptom(cough).
corona_symptom(trouble_breathing).
corona_symptom(fever).
corona_symptom(nosmell).
has_corona(frank).
has_symptom(alisha,cold).
has_symptom(alex,stomach_ache).
housemate(frank,eve).


person(mary).
person(john).
person(tabitha).
public_building(store).
public_building(museum).
public_building(municipality).
public_building(station).
activity(working).
activity(commuting).
activity(shopping).
activity(cycling).
activity(theatre).
activity(dance).
visit(store, shopping).
visit(station, commuting).
contact_profession(physiotherapy).
contact_profession(pedicure).
profession(mary, physiotherapy).
profession(john, pedicure).
profession(tabitha, scientist).
personal_mask_exception(john).
activity_mask_exception(theatre).
activity_mask_exception(dance).


stay_home(Person) :-
person(Person),
has_corona(Person).

stay_home(Person) :-
person(Person),
has_symptom(Person, S),
corona_symptom(S).

/*specify that this statement works in both directions*/
housemate(Person,Mate):- housemate(Mate, Person).

stay_home(Person):-
person(Person),
housemate(Person, Mate),
stay_home(Mate).


wear_mask(Activity,Person):-
activity(Activity),
person(Person),
(
(visit(Building, Activity),
public_building(Building));
(Activity = working,
profession(Person,Profession),
contact_profession(Profession))
),
\+ no_mask(Activity,Person).


/*wear_mask(working,Person):-
person(Person),
profession(Person,Profession),
contact_profession(Profession),
\+ no_mask(working,Person).*/


no_mask(Activity, Person):-
person(Person),
activity(Activity),
(personal_mask_exception(Person);
activity_mask_exception(Activity)).
