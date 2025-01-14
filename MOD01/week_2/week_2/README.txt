Danil Badarev 3210928
Wessel Ritskes 3212599

Basic assignment(2.24) + Both bonus assignments (2.25_A,2.25_B)

Our pearl.py makes use of methods we made ourselves that we put in dubs.py and merge.py, that's included those files
We used google.py to test our solution
In the Basic assigment(2.24) we did not change the file
Commands and Outcome:

Search term: pain
'pain' occurs in ['brian.txt', 'eyre.txt', 'manager.txt', 'metamorphosis.txt']

Search term: death
'death' occurs in ['brian.txt', 'eyre.txt', 'grail.txt', 'manager.txt', 'metamorphosis.txt']

Search term: suffering
'suffering' occurs in ['eyre.txt', 'metamorphosis.txt']


In the Bonus assignments (2.25_A) we changed line 23 (word_table = pearl.make_table(word_pairs) -> word_table = pearl.make_counted_table(word_pairs))
Commands and Outcome:

Search term: pain
'pain' occurs in [['eyre.txt', 17], ['metamorphosis.txt', 8], ['manager.txt', 1], ['brian.txt', 1]]

Search term: death
'death' occurs in [['eyre.txt', 20], ['grail.txt', 3], ['brian.txt', 2], ['metamorphosis.txt', 1], ['manager.txt', 1]]

Search term: suffering
'suffering' occurs in [['eyre.txt', 11], ['metamorphosis.txt', 1]]


In the Bonus assignments (2.25_B) we changed line 23 (word_table = pearl.make_table(word_pairs) -> word_table = pearl.make_density_table(word_pairs))
Commands and Outcome:

Search term: death
'death' occurs in [['manager.txt', 0.00083], ['grail.txt', 0.00023], ['brian.txt', 0.00014], ['eyre.txt', 0.00011], ['metamorphosis.txt', 5e-05]]

Search term: pain
'pain' occurs in [['manager.txt', 0.00083], ['metamorphosis.txt', 0.00036], ['eyre.txt', 9e-05], ['brian.txt', 7e-05]]

Search term: suffering
'suffering' occurs in [['eyre.txt', 6e-05], ['metamorphosis.txt', 5e-05]]