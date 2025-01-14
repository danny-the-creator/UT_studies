import matplotlib.pyplot as pl
import matplotlib.patches as mpatches
import numpy as np
reference_set = np.array([[1.4,0.2],[1.5,0.2],[1.7,0.4],[1.5,0.2],[1.5,0.1],[1.6,0.2],[1.1,0.1],[1.5,0.4],[1.4,0.3],[1.5,0.3],[1.5,0.4],[1.7,0.5],[1.6,0.2],[1.5,0.2],[1.6,0.2],[1.5,0.4],[1.4,0.2],[1.2,0.2],[1.4,0.1],[1.5,0.2],[1.3,0.3],[1.6,0.6],[1.4,0.3],[1.4,0.2],[1.4,0.2],[4.5,1.5],[4.,1.3],[4.5,1.3],[3.3,1.],[3.9,1.4],[4.2,1.5],[4.7,1.4],[4.4,1.4],[4.1,1.],[3.9,1.1],[4.,1.3],[4.7,1.2],[4.4,1.4],[5.,1.7],[3.5,1.],[3.7,1.],[5.1,1.6],[4.5,1.6],[4.4,1.3],[4.,1.3],[4.6,1.4],[3.3,1.],[4.2,1.2],[4.3,1.3],[4.1,1.3],[5.1,1.9],[5.6,1.8],[6.6,2.1],[6.3,1.8],[6.1,2.5],[5.3,1.9],[5.,2.],[5.3,2.3],[6.7,2.2],[5.,1.5],[4.9,2.],[4.9,1.8],[6.,1.8],[4.9,1.8],[5.8,1.6],[6.4,2.],[5.1,1.5],[6.1,2.3],[5.5,1.8],[5.4,2.1],[5.1,2.3],[5.9,2.3],[5.2,2.3],[5.2,2.],[5.1,1.8]])
reference_labels = np.array([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2])
test_set = np.array([[1.13,0.17],[1.37,0.4],[1.27,0.47],[1.05,0.28],[1.46,0.24],[1.14,0.08],[1.47,-0.14],[1.36,0.38],[1.16,0.88],[1.81,0.13],[1.26,-0.01],[1.16,0.42],[2.12,0.14],[1.89,0.37],[1.53,-0.11],[1.36,-0.19],[1.14,0.55],[1.34,0.12],[1.42,-0.16],[0.87,0.59],[1.11,0.07],[1.02,-0.2],[1.8,0.54],[1.67,0.53],[1.22,-0.13],[4.59,1.54],[4.56,1.72],[4.87,1.48],[4.33,1.76],[4.26,0.94],[3.42,1.21],[3.87,0.98],[3.45,1.4],[4.69,1.44],[4.7,1.21],[4.56,2.25],[5.,1.27],[4.36,1.16],[5.36,1.06],[4.61,1.19],[3.78,0.99],[3.77,1.34],[4.44,1.53],[4.76,1.47],[3.94,1.55],[4.65,1.18],[3.87,1.39],[4.06,1.13],[4.72,1.3],[2.61,1.35],[6.15,2.16],[5.9,2.04],[5.99,2.42],[4.7,1.51],[5.58,2.15],[4.46,2.11],[5.98,1.67],[4.76,2.12],[5.56,1.83],[7.03,2.43],[6.,2.69],[6.63,1.88],[6.04,2.11],[4.99,1.83],[5.31,1.98],[6.51,1.9],[5.22,2.12],[5.82,1.84],[5.75,2.58],[4.55,1.82],[5.9,2.45],[5.25,2.35],[5.76,2.21],[4.51,1.59],[5.58,2.41]])
test_label = np.array([0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2])
# plot REFERENCE SET
pl.scatter(reference_set[:, 0], reference_set[:, 1], c=reference_labels, s=60,
           marker='o', edgecolors='k', cmap=pl.cm.Paired)
pl.axis('equal')
pl.xlabel('petal length')
pl.ylabel('petal width')
pl.title('Iris Reference Set')
cm = pl.cm.get_cmap('Paired')
pl.legend(loc='lower right',
          handles=[mpatches.Patch(facecolor=cm(0.), edgecolor='k', label='Class 0'),
                  mpatches.Patch(facecolor=cm(0.5), edgecolor='k', label='Class 1'),
                  mpatches.Patch(facecolor=cm(1.), edgecolor='k', label='Class 2'),])
# pl.show()         #
# end PLOT REFERENCE SET


# plot TEST SET
pl.scatter(reference_set[:, 0], reference_set[:, 1], c=reference_labels, s=60,
           marker='o', edgecolors='k', cmap=pl.cm.Paired)
pl.scatter(test_set[:, 0], test_set[:, 1], c='red', s=60,
           marker='o', edgecolors='k')
pl.axis('equal')
pl.xlabel('petal length')
pl.ylabel('petal width')
pl.title('Iris Reference set with overlayed test samples (red dots)')
cm = pl.cm.get_cmap('Paired')
pl.legend(loc='lower right',
          handles=[mpatches.Patch(facecolor=cm(0.), edgecolor='k', label='Class 0'),
                  mpatches.Patch(facecolor=cm(0.5), edgecolor='k', label='Class 1'),
                  mpatches.Patch(facecolor=cm(1.), edgecolor='k', label='Class 2'),
                  mpatches.Patch(facecolor='red', edgecolor='k', label='Test samples'),])
# pl.show()             #


def knn(reference_set, ref_labels, test_sample, k):
    dist = []
    for referece_sample in reference_set:
        x = np.sqrt((referece_sample[0]-test_sample[0])**2 + (referece_sample[1]-test_sample[1])**2)
        dist.append(x)
    dist_ncl = {dist[n] : list(ref_labels)[n] for n in range(len(dist))}
    dist_ncl = {n : dist_ncl[n] for n in sorted(dist_ncl.keys())}
    nn = [n for n in list(dist_ncl.values())[:k]]
    return max(nn, key=nn.count)
# print(knn(reference_set, reference_labels, [5.76,2.21],5))



# print(result)
ks = [k for k in range(1, 20,2)]
acc_list = []
for k in ks:
    result = []
    for test_sample in test_set:
        x = knn(reference_set, reference_labels, test_sample, k)
        result.append(x)
    accuracy = len([n for n in range(len(result)) if result[n] == test_label[n]])/ len(test_label)
    acc_list.append(accuracy)
print(acc_list)