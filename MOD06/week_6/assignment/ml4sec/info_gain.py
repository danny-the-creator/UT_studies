from sklearn.preprocessing import LabelEncoder
from typing import List
import json
import numpy  as np
import pandas as pd
import requests

################################################################################
#                                   Entropy                                    #
################################################################################

def entropy(self, X: np.ndarray) -> float:
    """Computes the entropy of a variable X: H(X).

        The entropy is defined as:

        .. math::
           H(X) = - \sum_{i=1}^n p(x_i) \cdot \log_2 p(x_i)

        where :math:`p(x_i)` is the probability of observing :math:`x_i`.

        Parameters
        ----------
        X : np.array of shape=(n_samples,)
            Observed samples for which to compute the entropy.

        Returns
        -------
        result : float
            Entropy of X.
        """
    raise NotImplementedError(
        "You will need to implement the 'entropy()' function yourself."
    )


def conditional_entropy(self, X: np.ndarray, Y: np.ndarray) -> float:
    """Computes the conditional entropy of a variable Y given the observation X:
        H(Y|X).

        The conditional entropy is defined as:

        .. math::
           H(Y|X) = - \sum_{x \in X, y \in Y} p(x, y) \cdot \log_2 \\frac{p(x, y)}{p(x)}

        where :math:`p(x)` is the probability of observing :math:`x` and
        :math:`p(x, y)` is the joint probability, i.e. the probability of
        observing both :math:`x` and :math:`y` simultaneously.

        Parameters
        ----------
        X : np.array of shape=(n_samples,)
            Observations X.

        Y : np.array of shape=(n_samples,)
            Corresponding observation Y for which to compute the conditional
            entropy.

        Returns
        -------
        result : float
            Conditional entropy of Y given observation X.
        """
    raise NotImplementedError(
        "You will need to implement the 'conditional_entropy()' function "
        "yourself."
    )

################################################################################
#                                  Info Gain                                   #
################################################################################

def info_gain(self, features: np.ndarray, labels: np.ndarray) -> float:
    """Computes the information gain for a feature with respect to the labels.

        Parameters
        ----------
        features : np.array of shape=(n_samples,)
            Feature for which to compute the information gain (X).

        labels : np.array of shape=(n_samples,)
            Labels corresponding to features for which to compute the info gain
            (Y).

        Returns
        -------
        result : float
            Information gain.
        """
    # Compute the information gain:
    # The difference between entropy and conditional entropy
    return self.entropy(labels) - self.conditional_entropy(labels, features)


def show_info_gain(self, bins: int = 20) -> None:
    """Shows the information gain for all computed features.

        Parameters
        ----------
        bins : int, default=20
            Number of bins in which to catagorize each individual value.
        """
    # Get labels as numbers
    labels = LabelEncoder().fit_transform(self.labels_benign)

    # Get features in bins
    features = self.show_matrix().values
    features -= features.min(axis=0)
    features /= features.max(axis=0)
    features = (bins*features).astype(int)

    print("Information gain")
    print("-"*20)
    for feature in range(features.shape[1]):
        # Print information gain
        print("Feature {:2}: {:.6f}".format(
            feature,
            self.info_gain(features[:, feature], labels)
        ))

    print()

    # Compute overall info gain of features
    features = np.asarray([str(tuple(x)) for x in features])
    features = LabelEncoder().fit_transform(features)

    entropy   = self.entropy(labels)
    info_gain = self.info_gain(features, labels)

    # Print information gain
    print("Original entropy        : {:.6f}".format(entropy))
    print("Overall information gain: {:.6f}".format(info_gain))
    print("Final entropy           : {:.6f}".format(entropy - info_gain))


def submit_repair(
        self,
        student_numbers: List[str],
        server: str = "https://ml4sec.eemcs.utwente.nl/repair",
        debug: bool = False,
    ) -> None:
    """Submit your info gain implementation to the server to check if your
        computation is correct. The result will print whether you passed the
        repair or not.

        Parameters
        ----------
        student_numbers : list
            List of all student numbers in the group as a string, e.g.,
            's1234567'. Please use your actual student numbers, we have build in
            checks to prevent fraud.

        server : string, default="https://ml4sec.eemcs.utwente.nl/repair"
            Address of server to submit assignment.

        debug : boolean, default=False
            If True, prints the computed results
        """
    # Check if users are passed as a set or list
    if not isinstance(student_numbers, (list, set)):
        raise ValueError("Please pass your student numbers as a list.")

    # Load data
    data = pd.read_csv('data/repair.csv', index_col=False)
    features = data['features'].values
    labels   = data['labels'  ].values

    # Compute result
    data = {
        "student_numbers"    : student_numbers,
        'entropy'            : self.entropy(labels),
        'conditional entropy': self.conditional_entropy(labels, features),
        'information gain'   : self.info_gain(features, labels)
    }

    if debug:
        print("Submitting:")
        print("-"*40)
        print("student_numbers    : {}".format(repr(data.get("student_numbers"))))
        print("entropy            : {}".format(repr(data.get("entropy"))))
        print("conditional entropy: {}".format(repr(data.get("conditional entropy"))))
        print("information gain   : {}".format(repr(data.get("information gain"))))
        print()

    # Submit data
    r = requests.post(server, json=data)
    # Read response
    try:
        r = json.loads(r.text)
    except Exception as ex:
        print(
            "Could not read server response: '{}'\n"
            "The server may be overloaded because many students are submitting "
            "their assignment. Please try to submit again in a few minutes. If "
            "this problem persists for a longer time, please contact "
            "t.s.vanede@utwente.nl.\n"
            .format(ex)
        )
        r = {}

    # Print errors if any
    if len(r.get('errors', [])) > 0:
        print("Errors found:")
        for error in r.get('errors'):
            print("    - {}".format(error))
        print()

    print("Your results for the repair")
    print("---------------------------")
    print("entropy            : {}".format(r.get('entropy'            , 'error')))
    print("conditional entropy: {}".format(r.get('conditional entropy', 'error')))
    print("information gain   : {}".format(r.get('information gain'   , 'error')))
    print("")
    print(r.get('passed', 'You have not yet passed the repair.'))
