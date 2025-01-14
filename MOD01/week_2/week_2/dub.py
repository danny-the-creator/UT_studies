# Danil Badarev 3210928
# Wessel Ritskes 3212599


from util import words
def remove_dubs(data):
    res = []
    if len(data) != 0:
        fresh = data[0]
        i = 1
        while i < len(data):
            if data[i] != fresh:
                res.append(fresh)
                fresh = data[i]
            i += 1
        res.append(fresh)
    return res

def remove_dubs_count(pairs):
    res = []                    # We make a variable to store the results in
    if len(pairs) != 0:         # Check to make sure the program doesnt crash with the wrong (an empty) input
        fresh = pairs[0]        # We set fresh equal to the first element in the list of pairs
        file = [pairs[0][1],1]  # We set file equal to a pair containing the file name and the number of times it was found duplicated
        # print(file)
        i = 1
        while i < len(pairs):
            if pairs[i] != fresh:               # Check wether the current element is equal to the one in fresh,
                                                # to be clear we're looking at pairs, so we're looking for the same word and the same file name
                res.append([fresh[0], file])    # If its not equal then we add a new pair of [the word, [file name, word count]]
                fresh = pairs[i]                # Then we prepare the program for the next iteration of the loop by setting fresh to the new pair we found
                file = [pairs[i][1],1]          # And setting file equal to a list containing the file name and word count
            else:                               # If the current element and fresh are equal
                file[1]+= 1                     # Then we increase the word count
            i += 1
        res.append([fresh[0], file])            # We add the last element to the list
    return res                                  # And return the result

def remove_dubs_count_density(pairs):
    word_count = {'eyre.txt': len(words('eyre.txt')),                       # Word count is a dictionary of all the file names with the amount of words in them,
                  'metamorphosis.txt': len(words('metamorphosis.txt')),     # using this we dont have to do that calculation for every word
                  'brian.txt': len(words('brian.txt')),
                  'grail.txt': len(words('grail.txt')),
                  'hacktest.txt': len(words('hacktest.txt')),
                  'bear.txt': len(words('bear.txt')),
                  'catstory.txt': len(words('catstory.txt')),
                  'enlightenment.txt': len(words('enlightenment.txt')),
                  'imbecile.txt': len(words('imbecile.txt')),
                  'ramen.txt': len(words('ramen.txt')),
                  'roll.txt': len(words('roll.txt')),
                  'manager.txt': len(words('manager.txt')),
                  'oxymoron.txt': len(words('oxymoron.txt'))}
    res = []                        # We make a variable to store the results in
    if len(pairs) != 0:             # Check to make sure the program doesnt crash with the wrong (an empty) input
        fresh = pairs[0]            # We set fresh equal to the first element in the list of pairs
        file = [pairs[0][1],1]      # We set file equal to a pair containing the file name and the number of times it was found duplicated
        # print(file)
        i = 1
        while i < len(pairs):
            if pairs[i] != fresh:   # Check wether the current element is equal to the one in fresh,
                file[1] = round(file[1]/word_count[file[0]],5)  # We calculate the density of the word using the calculation:
                                                                # Amount of words we found / the total amount of words found in the file
                                                                # And then rounded it on 5 decimal points
                res.append([fresh[0], file])    # If its not equal then we add a new pair of [the word, [file name, word count]]
                fresh = pairs[i]                # Then we prepare the program for the next iteration of the loop by setting fresh to the new pair we found
                file = [pairs[i][1],1]          # And setting file equal to a list containing the file name and word count
            else:                               # If the current element and fresh are equal
                file[1]+= 1                     # Then we increase the word count
            i += 1
        file[1] = round(file[1]/word_count[file[0]],5) # Same density calculation as above
        res.append([fresh[0], file])            # We add the last element to the list

    return res                                  # And return the result

    # print(word_count)
    # return
# print(remove_dubs_count([['hello', 'aaaaaa'],['hello', 'aaaaaa'],['hello', 'aaaaaa'],['hello', 'bbbb'], ['Me','bbbbbbbbb'], ['World','cccccccccccc'], ['World','cccccccccccc'],['World','cccccccccccc'],['Mine','dddddddddddddd']]))