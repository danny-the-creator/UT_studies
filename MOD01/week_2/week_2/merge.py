# Danil Badarev 3210928
# Wessel Ritskes 3212599

def merge(data):
    if len(data) < 2:
        return data[:]
    else:
        fst = merge(data[:len(data) // 2])
        snd = merge(data[len(data) // 2:])

        res = []
        fi = 0
        si = 0

        while fi < len(fst) and si < len(snd):
            if fst[fi] < snd[si]:
                res.append(fst[fi])
                fi += 1
            else:
                res.append(snd[si])
                si += 1

        if fi < len(fst):
            res.extend(fst[fi:])
        elif si < len(snd):
            res.extend(snd[si:])

    return res
def merge_pairs(data):
    if len(data) < 2:
        return data[:]
    else:
        fst = merge_pairs(data[:len(data) // 2])
        snd = merge_pairs(data[len(data) // 2:])

        res = []
        fi = 0
        si = 0

        while fi < len(fst) and si < len(snd):
            if fst[fi][1] < snd[si][1] or (fst[fi][1] == snd[si][1] and fst[fi][0]<snd[si][0]):     # We adjusted the if statement to prioritize the second element of the pair
                res.append(fst[fi])
                fi += 1
            else:
                res.append(snd[si])
                si += 1

        if fi < len(fst):
            res.extend(fst[fi:])
        elif si < len(snd):
            res.extend(snd[si:])

    return res

