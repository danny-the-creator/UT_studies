# Danil Badarev 3210928
# Wessel Ritskes 3212599


from util import all_word_pairs,words
from dub import remove_dubs, remove_dubs_count,remove_dubs_count_density
from merge import merge, merge_pairs

def make_table(pairs):
    '''2.24 Basic assignment'''
    pairs = remove_dubs(merge(pairs)) # We remove all the duplicates using our function created during the previous assignments, so we also need to sort the list,
                                      # we do that using the merge method made during the previous assignments

    result = []                                 # A variable to store the results in
    if len(pairs) != 0:                         # Just in case 'pairs' is empty, we catch that using an if statement because otherwise it would throw an error
        fresh = pairs[0][0]                     # Set fresh equal to the first word
        file = [pairs[0][1]]                    # Set file equal to a list containing the first file we found the word in 'fresh' in
        i = 1
        while i < len(pairs):
            if pairs[i][0] != fresh:            # Check wether the current word in the loop is the same as the word in 'fresh'
                result.append([fresh, file])    # If it's not equal then we add the pair [fresh, file] to the results
                fresh = pairs[i][0]             # We set fresh equal to the new word we found
                file = [pairs[i][1]]            # We set file equal to new list containing the name of the file we found the new word in
            else:                               # If it is equal, then we add the file name to the list of 'file'
                file.append(pairs[i][1])
            i += 1
        result.append([fresh, file])            # At the end we append the last pair [fresh, file]
    return result                               # And return the results

def make_counted_table(pairs):
    '''2.25 Bonus assignments A'''
    pairs = remove_dubs_count(merge(pairs))
    result = []                                 # A variable to store the results in
    if len(pairs) != 0:                         # Just in case 'pairs' is empty, we catch that using an if statement because otherwise it would throw an error
        fresh = pairs[0][0]                     # Set fresh equal to the first word
        file = [pairs[0][1]]                    # Set file equal to a list containing the first file we found the word in 'fresh' in
        i = 1
        while i < len(pairs):
            if pairs[i][0] != fresh:            # Check wether the current word in the loop is the same as the word in 'fresh'
                result.append([fresh, merge_pairs(file)[::-1]])    # If it's not equal then we add the pair [fresh, file] to the results
                                                # But other than the make_table we also sort the 'file' list and reverse the list, for this we use merge_pairs instead of merge
                                                # Which is different than the merge_pairs we made during the previous assignments
                fresh = pairs[i][0]             # We set fresh equal to the new word we found
                file = [pairs[i][1]]            # We set file equal to new list containing the name of the file we found the new word in
            else:
                file.append(pairs[i][1])
            i += 1
        result.append([fresh, merge_pairs(file)[::-1]])            # At the end we append the last pair [fresh, file], and like before we sorted 'file' and reversed it
    return result                               # And return the results

def make_density_table(pairs):
    '''2.25 Bonus assigment B'''
    pairs = remove_dubs_count_density(merge(pairs))
    result = []                                 # A variable to store the results in
    if len(pairs) != 0:                         # Just in case 'pairs' is empty, we catch that using an if statement because otherwise it would throw an error
        fresh = pairs[0][0]                     # Set fresh equal to the first word
        file = [pairs[0][1]]                    # Set file equal to a list containing the first file we found the word in 'fresh' in
        i = 1
        while i < len(pairs):
            if pairs[i][0] != fresh:                # Check wether the current word in the loop is the same as the word in 'fresh
                result.append([fresh, merge_pairs(file)[::-1]])         # If it's not equal then we add the pair [fresh, file] to the results
                                                    # But other than the make_table we also sort the 'file' list and reverse the list, for this we use merge_pairs instead of merge
                                                    # Which is different than the merge_pairs we made during the previous assignments
                fresh = pairs[i][0]                 # We set fresh equal to the new word we found
                file = [pairs[i][1]]                # We set file equal to new list containing the name of the file we found the new word in
            else:
                file.append(pairs[i][1])
            i += 1
        result.append([fresh, merge_pairs(file)[::-1]])   # At the end we append the last pair [fresh, file], and like before we sorted 'file' and reversed it
    return result                                   # And return the results