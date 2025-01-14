from typing import List, Optional
import json
import numpy as np
import requests

########################################################################
#                                Submit                                #
########################################################################

def submit(
        self,
        student_numbers: List[str],
        highscore_name: Optional[str] = None,
        server: str = "https://ml4sec.eemcs.utwente.nl/submit",
    ) -> None:
    """Submit your prediction to the server to check if the prediction of your
        unknown data is correct. The result will print whether you passed the
        assignment or not.

        Parameters
        ----------
        student_numbers : List[str]
            List of all student numbers in the group as a string, e.g.,
            's1234567'. Please use your actual student numbers, we have build in
            checks to prevent fraud.

        highscore_name : string, optional
            If given, your performance will be published on the highscore
            page under this name.

        server : str, default="https://ml4sec.eemcs.utwente.nl/submit"
            Address of server to submit assignment.
        """
    # Check if users are passed as a set or list
    if not isinstance(student_numbers, (list, set)):
        raise ValueError("Please pass your student numbers as a list.")

    # Use benign data for training and unknown data for testing
    # Note that we use the minimum and maximum values from the training data to
    # scale the test data
    X_train, minimum, maximum = self.scale_numpy(self.feature_matrix(self.flows_benign))
    X_test , minimum, maximum = self.scale_numpy(
        self.feature_matrix(self.flows_unknown),
        minimum = minimum,
        maximum = maximum,
    )

    # Fit training data and predict testing data
    self.NIDS.fit(X_train)
    prediction = self.NIDS.predict(X_test)

    # Cast prediction to list of integers
    prediction = np.asarray(prediction, dtype=int).tolist()

    # Create JSON data to send
    data = {
        "prediction"     : prediction,
        "student_numbers": list(student_numbers),
        "name"           : highscore_name
    }

    # Submit data
    r = requests.post(server, json=data)
    # Read response
    try:
        r = json.loads(r.text)
    except Exception as e:
        print(
            "SERVER SIDE ERROR: '{}'. please contact t.s.vanede@utwente.nl."
            .format(e)
        )
        r = {}

    # Print errors, if any
    if len(r.get('errors', [])) > 0:
        print("Errors found:")
        for error in r.get('errors'):
            print("    - {}".format(error))
        print()

    # Print warnings, if any
    if len(r.get('warnings', [])) > 0:
        print("Warnings found:")
        for warning, message in r.get('warnings', {}).items():
            print("    - {}: {}".format(warning, message))
        print()

    # Show performance
    self.show_report(
        tpr      = r.get('tpr'     , float('NaN')),
        tnr      = r.get('tnr'     , float('NaN')),
        fpr      = r.get('fpr'     , float('NaN')),
        fnr      = r.get('fnr'     , float('NaN')),
        accuracy = r.get('accuracy', float('NaN')),

        precision = r.get('precision', float('NaN')),
        recall    = r.get('recall'   , float('NaN')),
        f1_score  = r.get('f1-score' , float('NaN')),
    )

    # Check if you passed
    if r.get('accuracy', 0) > 0.90 and r.get('fpr', 1) < 0.05:
        print("You have passed the assignment!")
    else:
        print("You have not yet passed the assignment.")
