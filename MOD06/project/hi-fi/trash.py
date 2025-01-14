import numpy as np
def TP(y_true: np.ndarray, y_pred: np.ndarray) -> int:
    both_labels = list(zip(y_pred, y_true))
    return both_labels.count((-1,-1))


def TN(y_true: np.ndarray, y_pred: np.ndarray) -> int:
    both_labels = list(zip(y_pred, y_true))
    return both_labels.count((1, 1))

def FP(y_true: np.ndarray, y_pred: np.ndarray) -> int:
    both_labels = list(zip(y_pred, y_true))
    return both_labels.count((-1, 1))


def FN(y_true: np.ndarray, y_pred: np.ndarray) -> int:
    both_labels = list(zip(y_pred, y_true))
    return both_labels.count((1, -1))

print(FP([1,-1,1],[-1,-1,1]))