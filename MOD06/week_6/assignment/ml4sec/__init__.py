class Assignment(object):

    def __init__(self, file_benign: str, file_unknown: str):
        """ML4sec assignment.
            Acts as backend for the ML4sec assignment. We use this to abstract
            away some of the functionality to make the assignment less confusing
            for students.

            Parameters
            ----------
            file_benign : str
                Path from which to load benign.csv.

            file_unknown : str
                Path from which to load unknown.csv.
        """
        # Load data
        self.data_benign  = self.load(file_benign)
        self.data_unknown = self.load(file_unknown)

        # Transform to flows
        self.flows_benign , self.labels_benign  = self.flows(self.data_benign )
        self.flows_unknown, self.labels_unknown = self.flows(self.data_unknown)

    # Import methods
    from .load      import load, flows
    from .extract   import extract, feature_matrix, show_matrix, test_extract
    from .info_gain import entropy, conditional_entropy, info_gain,\
                           show_info_gain, submit_repair
    from .scale     import scale, test_scale, test_scale_single, assert_scale, \
                           show_scaled, plot_scaled, plot_data, scale_numpy
    from .kernel    import soft_score, plot_kernels, _plot_kernel_
    from .split     import split, split_numpy, get_split, test_split, \
                           assert_split
    from .metrics   import TP, TN, FP, FN, TPR, TNR, FPR, FNR, accuracy, \
                           precision, recall, f1_score, prediction_report, \
                           show_report, test_metrics
    from .submit    import submit
