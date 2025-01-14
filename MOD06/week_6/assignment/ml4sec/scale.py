from sklearn.decomposition import PCA
from typing import Optional, Tuple
from .custom_types import Arraylike
import matplotlib.pyplot as plt
import numpy             as np
import pandas            as pd

################################################################################
#                                   Scaling                                    #
################################################################################

def scale(
        self,
        matrix: np.ndarray,
        minimum: Optional[np.ndarray] = None,
        maximum: Optional[np.ndarray] = None,
    ) -> Tuple[Arraylike, Arraylike, Arraylike]:
    """Scale features in matrix.

        Parameters
        ----------
        matrix : np.array of shape=(n_samples, n_features)
            Matrix to scale.

        minimum : array-like of shape=(n_features,), optional
            If given, should contain the minimum values for each feature to
            scale with.

        maximum : array-like of shape=(n_features,), optional
            If given, should contain the maximum values for each feature to
            scale with.

        Returns
        -------
        scaled_matrix : array-like of shape=(n_samples, n_features)
            Scaled matrix.

        minimum : array-like of shape=(n_features,)
            The minimum values for each feature used for scaling.

        maximum : array-like of shape=(n_features,)
            The maximum values for each feature used for scaling.
        """
    raise NotImplementedError(
        "You will need to implement the 'scale()' function yourself."
    )

################################################################################
#                                Scale as numpy                                #
################################################################################

def scale_numpy(
        self,
        matrix: np.ndarray,
        minimum: Optional[np.ndarray] = None,
        maximum: Optional[np.ndarray] = None,
    ) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Scale features in matrix to numpy arrays.

        Parameters
        ----------
        matrix : np.array of shape=(n_samples, n_features)
            Matrix to scale.

        minimum : array-like of shape=(n_features,), optional
            If given, should contain the minimum values for each feature to
            scale with.

        maximum : array-like of shape=(n_features,), optional
            If given, should contain the maximum values for each feature to
            scale with.

        Returns
        -------
        scaled_matrix : np.array of shape=(n_samples, n_features)
            Scaled matrix.

        minimum : np.array of shape=(n_features,)
            The minimum values for each feature used for scaling.

        maximum : np.array of shape=(n_features,)
            The maximum values for each feature used for scaling.
        """
    # Perform scaling
    scaled_matrix, minimum, maximum = self.scale(matrix, minimum, maximum)

    # Transform to numpy arrays
    scaled_matrix = np.asarray(scaled_matrix)
    minimum       = np.asarray(minimum)
    maximum       = np.asarray(maximum)

    # Return result
    return scaled_matrix, minimum, maximum

################################################################################
#                          Perform checks on scaling                           #
################################################################################

def test_scale(self, verbose: bool = True) -> None:
    """Method that runs some tests on data scaling.

        Parameters
        ----------
        verbose : boolean, default=True
            If True, print test cases.
        """

    ########################################################################
    #                             Test case 1                              #
    ########################################################################

    # Input
    matrix = np.asarray([
        [0, 1],
        [2, 3],
        [4, 5],
        [6, 7],
        [8, 9],
    ])
    minimum = None
    maximum = None

    # Target output
    target_scaled = np.asarray([
        [0   , 0],
        [0.25, 0.25],
        [0.5 , 0.5],
        [0.75, 0.75],
        [1   , 1],
    ])
    target_minimum = np.asarray([0, 1])
    target_maximum = np.asarray([8, 9])

    # Run single test case
    self.test_scale_single(
        scaled_input   = matrix,
        minimum_input  = minimum,
        maximum_input  = maximum,
        scaled_target  = target_scaled,
        minimum_target = target_minimum,
        maximum_target = target_maximum,
        verbose        = verbose,
    )

    # ########################################################################
    # #                             Test case 2                              #
    # ########################################################################

    # Input
    matrix = np.asarray([
        [0, 1, 10],
        [2, 3, 11],
        [4, 5, 12],
        [6, 7, 13],
        [8, 9, 14],
    ])
    minimum = np.asarray([4, -20, 0])
    maximum = np.asarray([6,  20, 1])

    # Target output
    target_scaled = np.asarray([
        [-2, 0.525, 10],
        [-1, 0.575, 11],
        [0 , 0.625, 12],
        [1 , 0.675, 13],
        [2 , 0.725, 14],
    ])
    target_minimum = np.asarray([4, -20, 0])
    target_maximum = np.asarray([6,  20, 1])

    # Run single test case
    self.test_scale_single(
        scaled_input   = matrix,
        minimum_input  = minimum,
        maximum_input  = maximum,
        scaled_target  = target_scaled,
        minimum_target = target_minimum,
        maximum_target = target_maximum,
        verbose        = verbose,
    )

    ########################################################################
    #                        Print success message                         #
    ########################################################################

    # Print success message
    print("All tests passed.")


def test_scale_single(self,
        scaled_input: np.ndarray,
        minimum_input: np.ndarray,
        maximum_input: np.ndarray,
        scaled_target: np.ndarray,
        minimum_target: np.ndarray,
        maximum_target: np.ndarray,
        verbose = False,
    ) -> None:
    """Perform a single test case of input and target.

        Parameters
        ----------
        scaled_input : np.array of shape=(n_samples, n_features)
            matrix input given to scale function.

        minimum_input : np.array of shape=(n_features), optional
            minimum input given to scale function.

        maximum_input : np.array of shape=(n_features), optional
            maximum input given to scale function.

        scaled_target : np.array of shape=(n_samples, n_features)
            Target scaled matrix if scale is implemented correctly.

        minimum_target : np.array of shape=(n_features)
            Target minimum of features if scale is implemented correctly.

        maximum_target : np.array of shape=(n_features)
            Target maximum of features if scale is implemented correctly.

        verbose : boolean, default=False
            If True, print information on test case.
        """

    # If verbose, print test case
    if verbose:
        print("Test case:")
        print("matrix  = \n{}".format(scaled_input))
        print("minimum = {}"  .format(minimum_input))
        print("maximum = {}\n".format(maximum_input))


    # Call scale function
    output = self.scale_numpy(
        matrix  = scaled_input,
        minimum = minimum_input,
        maximum = maximum_input,
    )

    # Perform checks
    self.assert_scale(
        scaled_target, minimum_target, maximum_target,
        *output,
    )


def assert_scale(self,
        scaled_target: Arraylike,
        minimum_target: Arraylike,
        maximum_target: Arraylike,
        scaled_output: Arraylike = None,
        minimum_output: Arraylike = None,
        maximum_output: Arraylike = None,
    ) -> None:
    """Performs checks comparing a computed output and target output.

        Parameters
        ----------
        scaled_target : array-like of shape=(n_samples, n_features)
            Target scaled matrix if scale is implemented correctly.

        minimum_target : array-like of shape=(n_features)
            Target minimum of features if scale is implemented correctly.

        maximum_target : array-like of shape=(n_features)
            Target maximum of features if scale is implemented correctly.

        scaled_output : array-like of shape=(n_samples, n_features)
            Scaled output by running it through the scale implementation.

        minimum_output : array-like of shape=(n_features)
            Minimum of features computed by scale implementation.

        maximum_output : array-like of shape=(n_features)
            Maximum of features computed by scale implementation.
        """

    ########################################################################
    #                       Check if output is given                       #
    ########################################################################

    """Perform check on scale implementation to check for common bugs."""
    # Check if scaled matrix is returned
    if scaled_output is None:
        raise ValueError(
            "Your method did not return a scaled matrix. Please return:\n"
            " - the scaled matrix\n"
            " - minimum value for each column\n"
            " - maximum value for each column\n"
        )

    # Check if minimum is returned
    if minimum_output is None:
        raise ValueError(
            "Your method did not return a minimum value. Please return:\n"
            " - the scaled matrix\n"
            " - minimum value for each column\n"
            " - maximum value for each column\n"
        )

    # Check if maximum is returned
    if minimum_output is None:
        raise ValueError(
            "Your method did not return a maximum value. Please return:\n"
            " - the scaled matrix\n"
            " - minimum value for each column\n"
            " - maximum value for each column\n"
        )

    ########################################################################
    #                 Check if output is given as an array                 #
    ########################################################################

    # Transform arrays to numpy
    try:
        scaled_output  = np.asarray(scaled_output )
        minimum_output = np.asarray(minimum_output)
        maximum_output = np.asarray(maximum_output)
    except Exception as e:
        raise ValueError("Your could not be cast to array: '{}'".format(e))

    # Transform arrays to numpy
    try:
        scaled_target  = np.asarray(scaled_target )
        minimum_target = np.asarray(minimum_target)
        maximum_target = np.asarray(maximum_target)
    except Exception as e:
        raise ValueError(
            "Target array could not be cast to array: '{}'. If you called the "
            "'assert_scale' method yourself, please check if your input is "
            "correct. If you get this message when running test_scale, please "
            "contact t.s.vanede@utwente.nl".format(e)
        )

    ########################################################################
    #                  Check if output shapes are correct                  #
    ########################################################################

    # Check if minimum is of correct shape
    if minimum_output.shape[0] != scaled_target.shape[1]:
        raise ValueError(
            "The size of your computed minimum ({}) did not match the expected "
            "size ({}). Minimum should be computed based on the features "
            "(columns). Please check if you did not accidentally compute the "
            "minimum over the samples (rows) instead.".format(
            minimum_output.shape[0], scaled_target.shape[1]
        ))

    # Check if minimum is of correct shape
    if minimum_output.shape != minimum_target.shape:
        raise ValueError(
            "The size of your computed minimum ({}) did not match the expected "
            "size ({})".format(minimum_output.shape, minimum_target.shape)
        )

    # Check if maximum is of correct shape
    if maximum_output.shape[0] != scaled_target.shape[1]:
        raise ValueError(
            "The size of your computed maximum ({}) did not match the expected "
            "size ({}). Maximum should be computed based on the features "
            "(columns). Please check if you did not accidentally compute the "
            "maximum over the samples (rows) instead.".format(
            maximum_output.shape[0], scaled_target.shape[1]
        ))

    # Check if maximum is of correct shape
    if maximum_output.shape != maximum_target.shape:
        raise ValueError(
            "The size of your computed maximum ({}) did not match the expected "
            "size ({})".format(maximum_output.shape, maximum_target.shape)
        )

    # Check if scaled matrix is of correct shape
    if scaled_output.shape != scaled_target.shape:
        raise ValueError(
            "The size of your computed scaled matrix ({}) did not match the "
            "expected size ({})".format(scaled_output.shape,
            scaled_target.shape
        ))

    ########################################################################
    #                  Check if output values are correct                  #
    ########################################################################

    # Check if computed minimum is correct
    if not np.all(minimum_output == minimum_target):
        raise ValueError(
            "Minimum was incorrectly computed. Expected minimum to be:\n{}\n, "
            "but minimum was:\n{}\n".format(minimum_target, minimum_output)
        )

    # Check if computed maximum is correct
    if not np.all(maximum_output == maximum_target):
        raise ValueError(
            "Maximum was incorrectly computed. Expected maximum to be:\n{}\n, "
            "but maximum was:\n{}\n".format(maximum_target, maximum_output)
        )

    # Check if computed scaled matrix is correct
    if not np.all(scaled_output == scaled_target):
        raise ValueError(
            "Scaled matrix was incorrectly computed. Expected scaled matrix to "
            "be:\n{}\n, but scaled matrix was:\n{}\n".format(scaled_target,
            scaled_output,
        ))


################################################################################
#                                Visualisation                                 #
################################################################################

def show_scaled(self) -> pd.DataFrame:
    """Shows the scaled feature matrix for benign flows.

        1. Extracts the feature matrix.
        2. Scales the data.
        3. Turns it into a pd.DataFrame.

        """
    return pd.DataFrame(self.scale_numpy(self.feature_matrix(self.flows_benign))[0])


def plot_scaled(self) -> None:
    """Plot scaled vs unscaled.

        1. Computes feature matrix for both benign.csv and unknown.csv.
        2. Applies scaling to both benign and unknown feature matrix.
        3. Plots the differences.

        """
    # Get unscaled matrices
    X_unscaled_benign  = self.feature_matrix(self.flows_benign )
    X_unscaled_unknown = self.feature_matrix(self.flows_unknown)

    # Get scaled matrices
    X_scaled_benign , min_, max_ = self.scale_numpy(X_unscaled_benign)
    X_scaled_unknown, _, _ = self.scale_numpy(X_unscaled_unknown, min_, max_)

    # Create 2x2 grid
    fig, axs = plt.subplots(2, 2, figsize=(12, 8))

    # Create plots
    axs[0, 0].set_title("Unscaled data", fontsize=20)
    axs[0, 0].set_ylabel("Benign data", fontsize=20)
    self.plot_data(axs[0, 0], X_unscaled_benign, self.labels_benign)
    axs[0, 1].set_title("Scaled data", fontsize=20)
    self.plot_data(axs[0, 1], X_scaled_benign  , self.labels_benign)
    axs[0, 1].legend(loc='center left', bbox_to_anchor=(1, 0.5))
    axs[1, 0].set_ylabel("Unknown data", fontsize=20)
    self.plot_data(axs[1, 0], X_unscaled_unknown, self.labels_unknown)
    self.plot_data(axs[1, 1], X_scaled_unknown  , self.labels_unknown)
    axs[1, 1].legend(loc='center left', bbox_to_anchor=(1, 0.5))

    # Show plot
    plt.show()


def plot_data(self, ax: plt.axis, X: Arraylike, y: Arraylike) -> None:
    """Plots the feature vectors given by X and labelled by y.

        Parameters
        ----------
        ax : matplotlib.axis
            Axis on which to plot data.

        X : array-like of shape=(n_samples, n_features)
            Feature vectors to plot.

        y : array-like of shape=(n_features,)
            Labels corresponding to the feature vectors.
        """
    # Transform to numpy arrays
    X = np.asarray(X)
    y = np.asarray(y)

    # The PCA(n) takes all features from X and compresses them
    # into n dimensions, in our case to 2 dimensions for plotting.
    X = PCA(2).fit_transform(X)

    # Next for each label, we scatter the corresponding points
    for label in np.unique(y):
        ax.scatter(X[:, 0][y == label], X[:, 1][y == label], label=label)
