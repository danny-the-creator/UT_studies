import numpy  as np
import pandas as pd
from typing import List, Tuple
from .custom_types import Protocol

def load(self, infile: str) -> pd.DataFrame:
    """Loads input .csv file.

        Parameters
        ----------
        infile : str
            Path of input .csv file.

        Returns
        -------
        data : pd.DataFrame
            Pandas dataframe containing data loaded from csv file.
        """
    # Get data sorted by timestamps
    return pd.read_csv(infile).sort_values(by='timestamp')


def flows(self, dataframe: pd.DataFrame) -> Tuple[
        List[Tuple[Tuple[Protocol, str, int, str, int], pd.DataFrame]],
        np.ndarray,
    ]:
    """Group dataframe by flow tuple.

        Parameters
        ----------
        dataframe : pd.DataFrame
            DataFrame to group by flow tuple, defined as the 5-tuple:
            (protocol, src, sport, dst, dport).

        Returns
        -------
        flows : list
            List of (key, frame) tuple for each flow.
            Where key: 5-tuple (protocol, src, sport, dst, dport).
            And frame: pd.DataFrame().

        labels : np.array of shape=(n_flows,)
            Label corresponding to each flow.
        """
    # Group packets by flow
    flows = dataframe.groupby(["protocol", "src", "sport", "dst", "dport"])

    # Extract flows as list
    flows   = list(sorted(flows))
    # Extract label for each flow
    labels = np.asarray([frame['label'].values[0] for key, frame in flows])

    # Return flows and corresponding labels
    return flows, labels
