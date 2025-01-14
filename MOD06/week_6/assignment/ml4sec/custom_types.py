from typing import Literal, Union
import numpy as np

Protocol = Literal['TCP', 'UDP']
Arraylike = Union[np.ndarray, list, tuple]