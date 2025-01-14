# Danil Badarev 3210928
# Wessel Ritskes 3212599

def linear(data, value):
    """Return the index of 'value' in 'data', or -1 if it does not occur"""
    # Go through the data list from index 0 upwards
    i = 0
    # continue until value found or index outside valid range
    while i < len(data) and data[i] != value:
        # increase the index to go to the next data value
        if data[i] > value:
            break
        i = i + 1
    # test if we have found the value
    if i == len(data) or  data[i] > value:
        # no, we went outside valid range; return -1
        return -1
    else:
        # yes, we found the value; return the index
        return i

def binary(data, value):
    low = 0
    high = len(data)-1
    mid = len(data)//2
    while (high - low)!=-1 and data[mid]!= value:
        mid = (high + low)//2
        if value < data[mid]:
            high = mid-1
        else:
            low = mid +1
    return mid if data[mid] == value else -1

def binary_pairs(data, value):
    low = 0
    high = len(data) - 1
    mid = len(data) // 2
    while (high - low) != -1 and data[mid][0] != value:
        mid = (high + low) // 2
        if value < data[mid][0]:
            high = mid - 1
        else:
            low = mid + 1
    return mid if data[mid][0] == value else -1