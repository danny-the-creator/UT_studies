from ordsearch import linear
# print(linear([1,2,3,4,5,6],3))
# print(linear([1,3,7,9,10,23,67],10))
# print(linear([2,4,6,1,7,4],1))
#
# print(linear([1,2,3,5], 't'))
# print( linear ([ "a" , " short " , " sentence "], 2))
from util import lines
from ordsearch import binary
print(binary(lines('Unabr.dict'), 'eagle'))
print(binary(lines("Unabr.dict"), "zygose"))
print(binary([1, 20, 32, 42, 51, 68, 79, 81, 98], 32))
# print(binary([1,2,3,4,5,6],7))