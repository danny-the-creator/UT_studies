from sort import buble
from util import lines
from merge import merge
from random import shuffle
import time
# print(buble([45,3,78,1,34,6,8,0,10,-5,92,-10,15]))
# print(merge([45,3,78,1,34,6,8,0,10,-5,92,-10,15]))
start = time.time()
# print(buble(lines('Unabr.dict')))         # 213557
#
sh = lines('Unabr.dict')
shuffle(sh)
#
# res = merge(sh)
# res = sorted(sh)
# res1= buble(sh)
print(res)
# sorted(lines('Unabr.dict'))
#
# print(buble(lines('hacktest.txt.')))      # 825
# print(sorted(lines('hacktest.txt.')))

print(time.time() - start)
