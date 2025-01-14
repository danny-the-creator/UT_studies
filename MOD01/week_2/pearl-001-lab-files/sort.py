def buble(data):
    res = data.copy()
    ui = len(data) - 1
    while ui> 0:
        si = 0
        i = 0
        while i <ui:
            if res[i]>res[i+1]:
                res[i], res[i+1] = res[i+1], res[i]
                si = i
            i+=1
        ui = si
    return res
# print(my_sort([45,3,78,1,34,6,8,0,10,-5,92,-10,15]))