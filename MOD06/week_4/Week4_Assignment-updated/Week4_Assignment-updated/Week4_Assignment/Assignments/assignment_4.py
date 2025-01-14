# coding: UTF-8
import sys
l1l_m6ai_ = sys.version_info [0] == 2
l11l11l_m6ai_ = 2048
l1l11_m6ai_ = 7
def l1l1l_m6ai_ (l1ll11_m6ai_):
    global l11l1l1_m6ai_
    l1l1l11_m6ai_ = ord (l1ll11_m6ai_ [-1])
    l1l1l1l_m6ai_ = l1ll11_m6ai_ [:-1]
    l1lll11_m6ai_ = l1l1l11_m6ai_ % len (l1l1l1l_m6ai_)
    l1l1l1_m6ai_ = l1l1l1l_m6ai_ [:l1lll11_m6ai_] + l1l1l1l_m6ai_ [l1lll11_m6ai_:]
    if l1l_m6ai_:
        l1l1ll1_m6ai_ = unicode () .join ([l111l_m6ai_ (ord (char) - l11l11l_m6ai_ - (l11l11_m6ai_ + l1l1l11_m6ai_) % l1l11_m6ai_) for l11l11_m6ai_, char in enumerate (l1l1l1_m6ai_)])
    else:
        l1l1ll1_m6ai_ = str () .join ([chr (ord (char) - l11l11l_m6ai_ - (l11l11_m6ai_ + l1l1l11_m6ai_) % l1l11_m6ai_) for l11l11_m6ai_, char in enumerate (l1l1l1_m6ai_)])
    return eval (l1l1ll1_m6ai_)
# l11_m6ai_ l11ll_m6ai_
import numpy as np
import pandas as pd
from sklearn import tree
class Assignment:
    def __init__(self):
        self.assignment_dataset = pd.read_csv("dataset_IT_project_success.csv", skipinitialspace=True)
    def l1lllll_m6ai_(self, dataset, l11l_m6ai_):
        entropy = 0
        labels = dataset[l11l_m6ai_]
        for value in labels.value_counts():
            entropy = entropy - (value / dataset.shape[0]) * np.log2(value / dataset.shape[0])
        return entropy
    def test_entropy(self, function):
        l1lll_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠬࡌࡥࡢࡶࡸࡶࡪ࠷ࠧࠁ"): [l1l1l_m6ai_ (u"࠭ࡁࠨࠂ"), l1l1l_m6ai_ (u"ࠧࡃࠩࠃ"), l1l1l_m6ai_ (u"ࠨࡅࠪࠄ"), l1l1l_m6ai_ (u"ࠩࡄࠫࠅ"), l1l1l_m6ai_ (u"ࠪࡆࠬࠆ"), l1l1l_m6ai_ (u"ࠫࡈ࠭ࠇ")],
            l1l1l_m6ai_ (u"ࠬࡉ࡬ࡢࡵࡶࠫࠈ"): [l1l1l_m6ai_ (u"࡙࠭ࡦࡵࠪࠉ"), l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫࠊ"), l1l1l_m6ai_ (u"ࠨࡐࡲࠫࠋ"), l1l1l_m6ai_ (u"ࠩࡑࡳࠬࠌ"), l1l1l_m6ai_ (u"ࠪ࡝ࡪࡹࠧࠍ"), l1l1l_m6ai_ (u"ࠫࡓࡵࠧࠎ")]
        })
        l111l1_m6ai_ = self.l1lllll_m6ai_(l1lll_m6ai_, l1l1l_m6ai_ (u"ࠬࡉ࡬ࡢࡵࡶࠫࠏ"))
        l1l11l1_m6ai_ = function(l1lll_m6ai_, l1l1l_m6ai_ (u"࠭ࡃ࡭ࡣࡶࡷࠬࠐ"))
        if not isinstance(l1l11l1_m6ai_, float):
            raise ValueError(
                l1l1l_m6ai_ (u"ࠢࡕࡪࡨࠤ࡫ࡻ࡮ࡤࡶ࡬ࡳࡳࠦࡳࡩࡱࡸࡰࡩࠦࡲࡦࡶࡸࡶࡳࠦࡡࠡࡨ࡯ࡳࡦࡺࠬࠡࡤࡸࡸࠥࡸࡥࡵࡷࡵࡲࡪࡪࠠࠣࠑ") + type(l1l11l1_m6ai_).__name__ + l1l1l_m6ai_ (u"ࠣ࠰ࠥࠒ")
            )
        if not np.isclose(l1l11l1_m6ai_, l111l1_m6ai_, atol=1e-3):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠤࡗࡩࡸࡺࠠࡤࡣࡶࡩࠥ࠷ࠠࡧࡣ࡬ࡰࡪࡪ࠺ࠡࡇࡻࡴࡪࡩࡴࡦࡦࠣࡩࡳࡺࡲࡰࡲࡼࠤࠧࠓ") + str(l111l1_m6ai_) + l1l1l_m6ai_ (u"ࠥ࠰ࠥࡨࡵࡵࠢࡪࡳࡹࠦࠢࠔ") + str(l1l11l1_m6ai_) + l1l1l_m6ai_ (u"ࠦ࠳ࠦࠢࠕ"),
                l1l1l_m6ai_ (u"ࠧࡖ࡬ࡦࡣࡶࡩࠥ࡫࡮ࡴࡷࡵࡩࠥࡺࡨࡢࡶࠣࡽࡴࡻࠠࡢࡴࡨࠤࡨࡵࡲࡳࡧࡦࡸࡱࡿࠠࡢࡲࡳࡰࡾ࡯࡮ࡨࠢࡷ࡬ࡪࠦࡥ࡯ࡶࡵࡳࡵࡿࠠࡧࡱࡵࡱࡺࡲࡡ࠻ࠢࠥࠖ"),
                l1l1l_m6ai_ (u"ࠨࡅ࡯ࡶࡵࡳࡵࡿࠠ࠾ࠢ࠰ࡷࡺࡳࠨࡑࠪࡨ࠭ࠥ࠰ࠠ࡭ࡱࡪ࠶࠭ࡖࠨࡦࠫࠬ࠭࠳ࠨࠗ"),
            )
        l1l1_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠧࡇࡧࡤࡸࡺࡸࡥ࠲ࠩ࠘"): [l1l1l_m6ai_ (u"ࠨࡃࠪ࠙"), l1l1l_m6ai_ (u"ࠩࡅࠫࠚ"), l1l1l_m6ai_ (u"ࠪࡇࠬࠛ"), l1l1l_m6ai_ (u"ࠫࡆ࠭ࠜ"), l1l1l_m6ai_ (u"ࠬࡈࠧࠝ"), l1l1l_m6ai_ (u"࠭ࡁࠨࠞ"), l1l1l_m6ai_ (u"ࠧࡃࠩࠟ"), l1l1l_m6ai_ (u"ࠨࡅࠪࠠ"), l1l1l_m6ai_ (u"ࠩࡆࠫࠡ")],
            l1l1l_m6ai_ (u"ࠪࡇࡱࡧࡳࡴࠩࠢ"): [l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨࠣ"), l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩࠤ"), l1l1l_m6ai_ (u"࠭ࡎࡰࠩࠥ"), l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫࠦ"), l1l1l_m6ai_ (u"ࠨ࡛ࡨࡷࠬࠧ"), l1l1l_m6ai_ (u"ࠩ࡜ࡩࡸ࠭ࠨ"), l1l1l_m6ai_ (u"ࠪࡒࡴ࠭ࠩ"), l1l1l_m6ai_ (u"ࠫࡓࡵࠧࠪ"), l1l1l_m6ai_ (u"ࠬࡔ࡯ࠨࠫ")]
        })
        l111l1_m6ai_ = self.l1lllll_m6ai_(l1l1_m6ai_, l1l1l_m6ai_ (u"࠭ࡃ࡭ࡣࡶࡷࠬࠬ"))
        l1l11l1_m6ai_ = function(l1l1_m6ai_, l1l1l_m6ai_ (u"ࠧࡄ࡮ࡤࡷࡸ࠭࠭"))
        if not np.isclose(l1l11l1_m6ai_, l111l1_m6ai_, atol=1e-3):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠣࡖࡨࡷࡹࠦࡣࡢࡵࡨࠤ࠷ࠦࡦࡢ࡫࡯ࡩࡩࡀࠠࡆࡺࡳࡩࡨࡺࡥࡥࠢࡨࡲࡹࡸ࡯ࡱࡻࠣࠦ࠮") + str(l111l1_m6ai_) + l1l1l_m6ai_ (u"ࠤ࠯ࠤࡧࡻࡴࠡࡩࡲࡸࠥࠨ࠯") + str(l1l11l1_m6ai_) + l1l1l_m6ai_ (u"ࠥ࠲ࠥࠨ࠰"),
                l1l1l_m6ai_ (u"ࠦࡕࡲࡥࡢࡵࡨࠤࡪࡴࡳࡶࡴࡨࠤࡹ࡮ࡡࡵࠢࡷ࡬ࡪࠦࡦࡶࡰࡦࡸ࡮ࡵ࡮ࠡࡥࡤࡲࠥ࡮ࡡ࡯ࡦ࡯ࡩࠥࡪࡡࡵࡣࡶࡩࡹࡹࠠࡸ࡫ࡷ࡬ࠥࡻ࡮ࡦࡸࡨࡲࠥࡩ࡬ࡢࡵࡶࠤࡩ࡯ࡳࡵࡴ࡬ࡦࡺࡺࡩࡰࡰࡶ࠲ࠧ࠱")
            )
        l11ll1_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠬࡌࡥࡢࡶࡸࡶࡪ࠷ࠧ࠲"): [l1l1l_m6ai_ (u"࠭ࡁࠨ࠳"), l1l1l_m6ai_ (u"ࠧࡃࠩ࠴"), l1l1l_m6ai_ (u"ࠨࡅࠪ࠵"), l1l1l_m6ai_ (u"ࠩࡄࠫ࠶"), l1l1l_m6ai_ (u"ࠪࡆࠬ࠷"), l1l1l_m6ai_ (u"ࠫࡈ࠭࠸"), l1l1l_m6ai_ (u"ࠬࡊࠧ࠹"), l1l1l_m6ai_ (u"࠭ࡄࠨ࠺")],
            l1l1l_m6ai_ (u"ࠧࡄ࡮ࡤࡷࡸ࠭࠻"): [l1l1l_m6ai_ (u"ࠨ࡛ࡨࡷࠬ࠼"), l1l1l_m6ai_ (u"ࠩࡑࡳࠬ࠽"), l1l1l_m6ai_ (u"ࠪࡑࡦࡿࡢࡦࠩ࠾"), l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨ࠿"), l1l1l_m6ai_ (u"ࠬࡔ࡯ࠨࡀ"), l1l1l_m6ai_ (u"࠭ࡍࡢࡻࡥࡩࠬࡁ"), l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫࡂ"), l1l1l_m6ai_ (u"ࠨࡏࡤࡽࡧ࡫ࠧࡃ")]
        })
        l111l1_m6ai_ = self.l1lllll_m6ai_(l11ll1_m6ai_, l1l1l_m6ai_ (u"ࠩࡆࡰࡦࡹࡳࠨࡄ"))
        l1l11l1_m6ai_ = function(l11ll1_m6ai_, l1l1l_m6ai_ (u"ࠪࡇࡱࡧࡳࡴࠩࡅ"))
        if not np.isclose(l1l11l1_m6ai_, l111l1_m6ai_, atol=1e-3):
            raise AssertionError(
                l1l1l_m6ai_ (u"࡙ࠦ࡫ࡳࡵࠢࡦࡥࡸ࡫ࠠ࠴ࠢࡩࡥ࡮ࡲࡥࡥ࠼ࠣࡉࡽࡶࡥࡤࡶࡨࡨࠥ࡫࡮ࡵࡴࡲࡴࡾࠦࠢࡆ") + str(l111l1_m6ai_) + l1l1l_m6ai_ (u"ࠧ࠲ࠠࡣࡷࡷࠤ࡬ࡵࡴࠡࠤࡇ") + str(l1l11l1_m6ai_) + l1l1l_m6ai_ (u"ࠨ࠮ࠡࠤࡈ"),
                l1l1l_m6ai_ (u"ࠢࡑ࡮ࡨࡥࡸ࡫ࠠࡦࡰࡶࡹࡷ࡫ࠠࡵࡪࡤࡸࠥࡺࡨࡦࠢࡩࡹࡳࡩࡴࡪࡱࡱࠤࡨࡵࡲࡳࡧࡦࡸࡱࡿࠠࡩࡣࡱࡨࡱ࡫ࡳࠡ࡯ࡸࡰࡹ࡯ࡰ࡭ࡧࠣࡧࡱࡧࡳࡴࡧࡶࠤ࡮ࡴࠠࡵࡪࡨࠤࡩࡧࡴࡢࡵࡨࡸ࠳ࠨࡉ")
            )
        l1ll1ll_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠨࡈࡨࡥࡹࡻࡲࡦ࠳ࠪࡊ"): [l1l1l_m6ai_ (u"ࠩࡄࠫࡋ"), l1l1l_m6ai_ (u"ࠪࡆࠬࡌ"), l1l1l_m6ai_ (u"ࠫࡈ࠭ࡍ"), l1l1l_m6ai_ (u"ࠬࡇࠧࡎ"), l1l1l_m6ai_ (u"࠭ࡂࠨࡏ"), l1l1l_m6ai_ (u"ࠧࡄࠩࡐ")],
            l1l1l_m6ai_ (u"ࠨࡅ࡯ࡥࡸࡹࠧࡑ"): [l1l1l_m6ai_ (u"ࠩ࡜ࡩࡸ࠭ࡒ"), l1l1l_m6ai_ (u"ࠪ࡝ࡪࡹࠧࡓ"), l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨࡔ"), l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩࡕ"), l1l1l_m6ai_ (u"࡙࠭ࡦࡵࠪࡖ"), l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫࡗ")]
        })
        l111l1_m6ai_ = self.l1lllll_m6ai_(l1ll1ll_m6ai_, l1l1l_m6ai_ (u"ࠨࡅ࡯ࡥࡸࡹࠧࡘ"))
        l1l11l1_m6ai_ = function(l1ll1ll_m6ai_, l1l1l_m6ai_ (u"ࠩࡆࡰࡦࡹࡳࠨ࡙"))
        if not np.isclose(l1l11l1_m6ai_, l111l1_m6ai_, atol=1e-3):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠥࡘࡪࡹࡴࠡࡥࡤࡷࡪࠦ࠴ࠡࡨࡤ࡭ࡱ࡫ࡤ࠻ࠢࡈࡼࡵ࡫ࡣࡵࡧࡧࠤࡪࡴࡴࡳࡱࡳࡽࠥࠨ࡚") + str(l111l1_m6ai_) + l1l1l_m6ai_ (u"ࠦ࠱ࠦࡢࡶࡶࠣ࡫ࡴࡺ࡛ࠠࠣ") + str(l1l11l1_m6ai_) + l1l1l_m6ai_ (u"ࠧ࠴ࠠࠣ࡜"),
                l1l1l_m6ai_ (u"ࠨࡐ࡭ࡧࡤࡷࡪࠦࡥ࡯ࡵࡸࡶࡪࠦࡴࡩࡣࡷࠤࡹ࡮ࡥࠡࡨࡸࡲࡨࡺࡩࡰࡰࠣࡧࡴࡸࡲࡦࡥࡷࡰࡾࠦࡨࡢࡰࡧࡰࡪࡹࠠࡥࡣࡷࡥࡸ࡫ࡴࡴࠢࡺ࡭ࡹ࡮ࠠࡻࡧࡵࡳࠥ࡫࡮ࡵࡴࡲࡴࡾࠦࠨࡪ࠰ࡨ࠲࠱ࠦࡡ࡭࡮ࠣࡰࡦࡨࡥ࡭ࡵࠣࡥࡷ࡫ࠠࡵࡪࡨࠤࡸࡧ࡭ࡦࠫ࠱ࠦ࡝")
            )
        l1l111l_m6ai_ = pd.read_csv(l1l1l_m6ai_ (u"ࠢࡥࡣࡷࡥࡸ࡫ࡴࡠࡋࡗࡣࡵࡸ࡯࡫ࡧࡦࡸࡤࡹࡵࡤࡥࡨࡷࡸ࠴ࡣࡴࡸࠥ࡞"), skipinitialspace=True)
        l111l1_m6ai_ = self.l1lllll_m6ai_(l1l111l_m6ai_, l1l1l_m6ai_ (u"ࠨࡒࡵࡳ࡯࡫ࡣࡵࠢࡖࡹࡨࡩࡥࡴࡵࠪ࡟"))
        l1l11l1_m6ai_ = function(l1l111l_m6ai_, l1l1l_m6ai_ (u"ࠩࡓࡶࡴࡰࡥࡤࡶࠣࡗࡺࡩࡣࡦࡵࡶࠫࡠ"))
        if not np.isclose(l1l11l1_m6ai_, l111l1_m6ai_, atol=1e-3):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠥࡘࡪࡹࡴࠡࡥࡤࡷࡪࠦ࠵ࠡࡨࡤ࡭ࡱ࡫ࡤ࠻ࠢࡈࡼࡵ࡫ࡣࡵࡧࡧࠤࡪࡴࡴࡳࡱࡳࡽࠥࠨࡡ") + str(l111l1_m6ai_) + l1l1l_m6ai_ (u"ࠦ࠱ࠦࡢࡶࡶࠣ࡫ࡴࡺࠠࠣࡢ") + str(l1l11l1_m6ai_) + l1l1l_m6ai_ (u"ࠧ࠴ࠠࠣࡣ"),
                l1l1l_m6ai_ (u"ࠨࡔࡩࡧࠣࡪࡺࡴࡣࡵ࡫ࡲࡲࠥࡹࡨࡰࡷ࡯ࡨࠥࡩ࡯ࡳࡴࡨࡧࡹࡲࡹࠡࡥࡤࡰࡨࡻ࡬ࡢࡶࡨࠤࡹ࡮ࡥࠡࡧࡱࡸࡷࡵࡰࡺࠢࡩࡳࡷࠦࡴࡩࡧࠣࡶࡪࡧ࡬ࠡࡦࡤࡸࡦࡹࡥࡵ࠰ࠥࡤ")
            )
    def l1ll11l_m6ai_(self, dataset, l11l_m6ai_, feature):
        l1l1lll_m6ai_ = 0
        for l11lll_m6ai_ in dataset[feature].unique():
            l1ll1l1_m6ai_ = dataset[dataset[feature] == l11lll_m6ai_]
            l1l1lll_m6ai_ = l1l1lll_m6ai_ + (l1ll1l1_m6ai_.shape[0] / dataset.shape[0]) * self.l1lllll_m6ai_(l1ll1l1_m6ai_, l11l_m6ai_)
        return self.l1lllll_m6ai_(dataset, l11l_m6ai_) - l1l1lll_m6ai_
    def test_information_gain(self, function):
            l1lll_m6ai_ = pd.DataFrame({
                l1l1l_m6ai_ (u"ࠧࡇࡧࡤࡸࡺࡸࡥ࠲ࠩࡥ"): [l1l1l_m6ai_ (u"ࠨࡃࠪࡦ"), l1l1l_m6ai_ (u"ࠩࡄࠫࡧ"), l1l1l_m6ai_ (u"ࠪࡆࠬࡨ"), l1l1l_m6ai_ (u"ࠫࡇ࠭ࡩ"), l1l1l_m6ai_ (u"ࠬࡉࠧࡪ"), l1l1l_m6ai_ (u"࠭ࡃࠨ࡫")],
                l1l1l_m6ai_ (u"ࠧࡄ࡮ࡤࡷࡸ࠭࡬"): [l1l1l_m6ai_ (u"ࠨ࡛ࡨࡷࠬ࡭"), l1l1l_m6ai_ (u"ࠩࡑࡳࠬ࡮"), l1l1l_m6ai_ (u"ࠪ࡝ࡪࡹࠧ࡯"), l1l1l_m6ai_ (u"ࠫࡓࡵࠧࡰ"), l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩࡱ"), l1l1l_m6ai_ (u"࠭ࡎࡰࠩࡲ")]
            })
            l11ll1l_m6ai_ = self.l1ll11l_m6ai_(l1lll_m6ai_, l1l1l_m6ai_ (u"ࠧࡄ࡮ࡤࡷࡸ࠭ࡳ"), l1l1l_m6ai_ (u"ࠨࡈࡨࡥࡹࡻࡲࡦ࠳ࠪࡴ"))
            l1_m6ai_ = function(l1lll_m6ai_, l1l1l_m6ai_ (u"ࠩࡆࡰࡦࡹࡳࠨࡵ"), l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬࡶ"))
            if not isinstance(l1_m6ai_, float):
                raise ValueError(
                    l1l1l_m6ai_ (u"࡙ࠦ࡮ࡥࠡࡨࡸࡲࡨࡺࡩࡰࡰࠣࡷ࡭ࡵࡵ࡭ࡦࠣࡶࡪࡺࡵࡳࡰࠣࡥࠥ࡬࡬ࡰࡣࡷ࠰ࠥࡨࡵࡵࠢࡵࡩࡹࡻࡲ࡯ࡧࡧࠤࠧࡷ") + type(l1_m6ai_).__name__ + l1l1l_m6ai_ (u"ࠧ࠴ࠢࡸ")
                )
            if not np.isclose(l1_m6ai_, l11ll1l_m6ai_, atol=1e-3):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠨࡔࡦࡵࡷࠤࡨࡧࡳࡦࠢ࠴ࠤ࡫ࡧࡩ࡭ࡧࡧ࠾ࠥࡋࡸࡱࡧࡦࡸࡪࡪࠠࡪࡰࡩࡳࡷࡳࡡࡵ࡫ࡲࡲࠥ࡭ࡡࡪࡰࠣࠦࡹ") + str(l11ll1l_m6ai_) + l1l1l_m6ai_ (u"ࠢ࠭ࠢࡥࡹࡹࠦࡧࡰࡶࠣࠦࡺ") + str(l1_m6ai_) + l1l1l_m6ai_ (u"ࠣ࠰ࠣࠦࡻ"),
                    l1l1l_m6ai_ (u"ࠤࡓࡰࡪࡧࡳࡦࠢࡨࡲࡸࡻࡲࡦࠢࡷ࡬ࡦࡺࠠࡺࡱࡸࠤࡦࡸࡥࠡࡥࡲࡶࡷ࡫ࡣࡵ࡮ࡼࠤࡦࡶࡰ࡭ࡻ࡬ࡲ࡬ࠦࡴࡩࡧࠣ࡭ࡳ࡬࡯ࡳ࡯ࡤࡸ࡮ࡵ࡮ࠡࡩࡤ࡭ࡳࠦࡦࡰࡴࡰࡹࡱࡧ࠮ࠣࡼ")
                )
            l1l1_m6ai_ = pd.DataFrame({
                l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬࡽ"): [l1l1l_m6ai_ (u"ࠫࡆ࠭ࡾ"), l1l1l_m6ai_ (u"ࠬࡇࠧࡿ"), l1l1l_m6ai_ (u"࠭ࡂࠨࢀ"), l1l1l_m6ai_ (u"ࠧࡃࠩࢁ"), l1l1l_m6ai_ (u"ࠨࡃࠪࢂ"), l1l1l_m6ai_ (u"ࠩࡅࠫࢃ"), l1l1l_m6ai_ (u"ࠪࡇࠬࢄ"), l1l1l_m6ai_ (u"ࠫࡈ࠭ࢅ"), l1l1l_m6ai_ (u"ࠬࡉࠧࢆ")],
                l1l1l_m6ai_ (u"࠭ࡃ࡭ࡣࡶࡷࠬࢇ"): [l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫ࢈"), l1l1l_m6ai_ (u"ࠨ࡛ࡨࡷࠬࢉ"), l1l1l_m6ai_ (u"ࠩࡑࡳࠬࢊ"), l1l1l_m6ai_ (u"ࠪࡒࡴ࠭ࢋ"), l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨࢌ"), l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩࢍ"), l1l1l_m6ai_ (u"࠭ࡎࡰࠩࢎ"), l1l1l_m6ai_ (u"ࠧࡏࡱࠪ࢏"), l1l1l_m6ai_ (u"ࠨࡐࡲࠫ࢐")]
            })
            l11ll1l_m6ai_ = self.l1ll11l_m6ai_(l1l1_m6ai_, l1l1l_m6ai_ (u"ࠩࡆࡰࡦࡹࡳࠨ࢑"), l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬ࢒"))
            l1_m6ai_ = function(l1l1_m6ai_, l1l1l_m6ai_ (u"ࠫࡈࡲࡡࡴࡵࠪ࢓"), l1l1l_m6ai_ (u"ࠬࡌࡥࡢࡶࡸࡶࡪ࠷ࠧ࢔"))
            if not np.isclose(l1_m6ai_, l11ll1l_m6ai_, atol=1e-3):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠨࡔࡦࡵࡷࠤࡨࡧࡳࡦࠢ࠵ࠤ࡫ࡧࡩ࡭ࡧࡧ࠾ࠥࡋࡸࡱࡧࡦࡸࡪࡪࠠࡪࡰࡩࡳࡷࡳࡡࡵ࡫ࡲࡲࠥ࡭ࡡࡪࡰࠣࠦ࢕") + str(l11ll1l_m6ai_) + l1l1l_m6ai_ (u"ࠢ࠭ࠢࡥࡹࡹࠦࡧࡰࡶࠣࠦ࢖") + str(l1_m6ai_) + l1l1l_m6ai_ (u"ࠣ࠰ࠣࠦࢗ"),
                    l1l1l_m6ai_ (u"ࠤࡓࡰࡪࡧࡳࡦࠢࡨࡲࡸࡻࡲࡦࠢࡷ࡬ࡦࡺࠠࡵࡪࡨࠤ࡫ࡻ࡮ࡤࡶ࡬ࡳࡳࠦࡨࡢࡰࡧࡰࡪࡹࠠࡶࡰࡨࡺࡪࡴࠠࡤ࡮ࡤࡷࡸࠦࡤࡪࡵࡷࡶ࡮ࡨࡵࡵ࡫ࡲࡲࡸࠦࡣࡰࡴࡵࡩࡨࡺ࡬ࡺ࠰ࠥ࢘")
                )
            l11ll1_m6ai_ = pd.DataFrame({
                l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵࢙ࠬ"): [l1l1l_m6ai_ (u"ࠫࡆ࢚࠭"), l1l1l_m6ai_ (u"ࠬࡈ࢛ࠧ"), l1l1l_m6ai_ (u"࠭ࡃࠨ࢜"), l1l1l_m6ai_ (u"ࠧࡂࠩ࢝"), l1l1l_m6ai_ (u"ࠨࡄࠪ࢞"), l1l1l_m6ai_ (u"ࠩࡆࠫ࢟"), l1l1l_m6ai_ (u"ࠪࡈࠬࢠ"), l1l1l_m6ai_ (u"ࠫࡉ࠭ࢡ"), l1l1l_m6ai_ (u"ࠬࡊࠧࢢ")],
                l1l1l_m6ai_ (u"࠭ࡃ࡭ࡣࡶࡷࠬࢣ"): [l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫࢤ"), l1l1l_m6ai_ (u"ࠨࡐࡲࠫࢥ"), l1l1l_m6ai_ (u"ࠩࡐࡥࡾࡨࡥࠨࢦ"), l1l1l_m6ai_ (u"ࠪ࡝ࡪࡹࠧࢧ"), l1l1l_m6ai_ (u"ࠫࡓࡵࠧࢨ"), l1l1l_m6ai_ (u"ࠬࡓࡡࡺࡤࡨࠫࢩ"), l1l1l_m6ai_ (u"࡙࠭ࡦࡵࠪࢪ"), l1l1l_m6ai_ (u"ࠧࡎࡣࡼࡦࡪ࠭ࢫ"), l1l1l_m6ai_ (u"ࠨࡏࡤࡽࡧ࡫ࠧࢬ")]
            })
            l11ll1l_m6ai_ = self.l1ll11l_m6ai_(l11ll1_m6ai_, l1l1l_m6ai_ (u"ࠩࡆࡰࡦࡹࡳࠨࢭ"), l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬࢮ"))
            l1_m6ai_ = function(l11ll1_m6ai_, l1l1l_m6ai_ (u"ࠫࡈࡲࡡࡴࡵࠪࢯ"), l1l1l_m6ai_ (u"ࠬࡌࡥࡢࡶࡸࡶࡪ࠷ࠧࢰ"))
            if not np.isclose(l1_m6ai_, l11ll1l_m6ai_, atol=1e-3):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠨࡔࡦࡵࡷࠤࡨࡧࡳࡦࠢ࠶ࠤ࡫ࡧࡩ࡭ࡧࡧ࠾ࠥࡋࡸࡱࡧࡦࡸࡪࡪࠠࡪࡰࡩࡳࡷࡳࡡࡵ࡫ࡲࡲࠥ࡭ࡡࡪࡰࠣࠦࢱ") + str(l11ll1l_m6ai_) + l1l1l_m6ai_ (u"ࠢ࠭ࠢࡥࡹࡹࠦࡧࡰࡶࠣࠦࢲ") + str(l1_m6ai_) + l1l1l_m6ai_ (u"ࠣ࠰ࠣࠦࢳ"),
                    l1l1l_m6ai_ (u"ࠤࡓࡰࡪࡧࡳࡦࠢࡨࡲࡸࡻࡲࡦࠢࡷ࡬ࡦࡺࠠࡵࡪࡨࠤ࡫ࡻ࡮ࡤࡶ࡬ࡳࡳࠦࡨࡢࡰࡧࡰࡪࡹࠠ࡮ࡷ࡯ࡸ࡮ࡶ࡬ࡦࠢࡦࡰࡦࡹࡳࡦࡵࠣࡧࡴࡸࡲࡦࡥࡷࡰࡾ࠴ࠢࢴ")
                )
            l1l1111_m6ai_ = pd.DataFrame({
                l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬࢵ"): [l1l1l_m6ai_ (u"ࠫࡆ࠭ࢶ"), l1l1l_m6ai_ (u"ࠬࡇࠧࢷ"), l1l1l_m6ai_ (u"࠭ࡂࠨࢸ"), l1l1l_m6ai_ (u"ࠧࡃࠩࢹ")],
                l1l1l_m6ai_ (u"ࠨࡅ࡯ࡥࡸࡹࠧࢺ"): [l1l1l_m6ai_ (u"ࠩ࡜ࡩࡸ࠭ࢻ"), l1l1l_m6ai_ (u"ࠪ࡝ࡪࡹࠧࢼ"), l1l1l_m6ai_ (u"ࠫࡓࡵࠧࢽ"), l1l1l_m6ai_ (u"ࠬࡔ࡯ࠨࢾ")]
            })
            l11ll1l_m6ai_ = self.l1lllll_m6ai_(l1l1111_m6ai_, l1l1l_m6ai_ (u"࠭ࡃ࡭ࡣࡶࡷࠬࢿ"))
            l1_m6ai_ = function(l1l1111_m6ai_, l1l1l_m6ai_ (u"ࠧࡄ࡮ࡤࡷࡸ࠭ࣀ"), l1l1l_m6ai_ (u"ࠨࡈࡨࡥࡹࡻࡲࡦ࠳ࠪࣁ"))
            if not np.isclose(l1_m6ai_, l11ll1l_m6ai_, atol=1e-3):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠤࡗࡩࡸࡺࠠࡤࡣࡶࡩࠥ࠺ࠠࡧࡣ࡬ࡰࡪࡪ࠺ࠡࡇࡻࡴࡪࡩࡴࡦࡦࠣ࡭ࡳ࡬࡯ࡳ࡯ࡤࡸ࡮ࡵ࡮ࠡࡩࡤ࡭ࡳࠦࠢࣂ") + str(l11ll1l_m6ai_) + l1l1l_m6ai_ (u"ࠥ࠰ࠥࡨࡵࡵࠢࡪࡳࡹࠦࠢࣃ") + str(l1_m6ai_) + l1l1l_m6ai_ (u"ࠦ࠳ࠦࠢࣄ"),
                    l1l1l_m6ai_ (u"࡚ࠧࡨࡦࠢࡩࡹࡳࡩࡴࡪࡱࡱࠤࡸ࡮࡯ࡶ࡮ࡧࠤࡨࡵࡲࡳࡧࡦࡸࡱࡿࠠࡪࡦࡨࡲࡹ࡯ࡦࡺࠢࡺ࡬ࡪࡴࠠࡢࠢࡩࡩࡦࡺࡵࡳࡧࠣࡴࡪࡸࡦࡦࡥࡷࡰࡾࠦࡳࡱ࡮࡬ࡸࡸࠦࡴࡩࡧࠣࡧࡱࡧࡳࡴࡧࡶ࠲ࠧࣅ")
                )
            l1l111l_m6ai_ = pd.read_csv(l1l1l_m6ai_ (u"ࠨࡤࡢࡶࡤࡷࡪࡺ࡟ࡊࡖࡢࡴࡷࡵࡪࡦࡥࡷࡣࡸࡻࡣࡤࡧࡶࡷ࠳ࡩࡳࡷࠤࣆ"), skipinitialspace=True)
            l11ll1l_m6ai_ = self.l1ll11l_m6ai_(l1l111l_m6ai_, l1l1l_m6ai_ (u"ࠧࡑࡴࡲ࡮ࡪࡩࡴࠡࡕࡸࡧࡨ࡫ࡳࡴࠩࣇ"), l1l1l_m6ai_ (u"ࠨࡔࡨࡵࡺ࡯ࡲࡦ࡯ࡨࡲࡹࡹࠠࡒࡷࡤࡰ࡮ࡺࡹࠨࣈ"))
            l1_m6ai_ = function(l1l111l_m6ai_, l1l1l_m6ai_ (u"ࠩࡓࡶࡴࡰࡥࡤࡶࠣࡗࡺࡩࡣࡦࡵࡶࠫࣉ"), l1l1l_m6ai_ (u"ࠪࡖࡪࡷࡵࡪࡴࡨࡱࡪࡴࡴࡴࠢࡔࡹࡦࡲࡩࡵࡻࠪ࣊"))
            if not np.isclose(l1_m6ai_, l11ll1l_m6ai_, atol=1e-3):
                raise AssertionError(
                    l1l1l_m6ai_ (u"࡙ࠦ࡫ࡳࡵࠢࡦࡥࡸ࡫ࠠ࠶ࠢࡩࡥ࡮ࡲࡥࡥ࠼ࠣࡉࡽࡶࡥࡤࡶࡨࡨࠥ࡯࡮ࡧࡱࡵࡱࡦࡺࡩࡰࡰࠣ࡫ࡦ࡯࡮ࠡࠤ࣋") + str(l11ll1l_m6ai_) + l1l1l_m6ai_ (u"ࠧ࠲ࠠࡣࡷࡷࠤ࡬ࡵࡴࠡࠤ࣌") + str(l1_m6ai_) + l1l1l_m6ai_ (u"ࠨ࠮ࠡࠤ࣍"),
                    l1l1l_m6ai_ (u"ࠢࡕࡪࡨࠤ࡫ࡻ࡮ࡤࡶ࡬ࡳࡳࠦࡳࡩࡱࡸࡰࡩࠦࡣࡰࡴࡵࡩࡨࡺ࡬ࡺࠢࡦࡥࡱࡩࡵ࡭ࡣࡷࡩࠥࡺࡨࡦࠢ࡬ࡲ࡫ࡵࡲ࡮ࡣࡷ࡭ࡴࡴࠠࡨࡣ࡬ࡲࠥ࡬࡯ࡳࠢࡷ࡬ࡪࠦࡲࡦࡣ࡯ࠤࡩࡧࡴࡢࡵࡨࡸ࠳ࠨ࣎")
                )
    def l111lll_m6ai_(self, dataset, l11l_m6ai_, l1ll1_m6ai_):
        l1lll1l_m6ai_ = []
        for feature in l1ll1_m6ai_:
            l1lll1l_m6ai_.append(self.l1ll11l_m6ai_(dataset, l11l_m6ai_, feature))
        return l1ll1_m6ai_[np.argmax(l1lll1l_m6ai_)]
    def test_feature_to_split_on(self, function):
        l1lll_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠨࡈࡨࡥࡹࡻࡲࡦ࠳࣏ࠪ"): [l1l1l_m6ai_ (u"ࠩࡄ࣐ࠫ"), l1l1l_m6ai_ (u"ࠪࡅ࣑ࠬ"), l1l1l_m6ai_ (u"ࠫࡇ࣒࠭"), l1l1l_m6ai_ (u"ࠬࡈ࣓ࠧ"), l1l1l_m6ai_ (u"࠭ࡃࠨࣔ"), l1l1l_m6ai_ (u"ࠧࡄࠩࣕ")],
            l1l1l_m6ai_ (u"ࠨࡈࡨࡥࡹࡻࡲࡦ࠴ࠪࣖ"): [l1l1l_m6ai_ (u"࡛ࠩࠫࣗ"), l1l1l_m6ai_ (u"ࠪ࡝ࠬࣘ"), l1l1l_m6ai_ (u"ࠫ࡝࠭ࣙ"), l1l1l_m6ai_ (u"ࠬ࡟ࠧࣚ"), l1l1l_m6ai_ (u"࠭ࡘࠨࣛ"), l1l1l_m6ai_ (u"࡚ࠧࠩࣜ")],
            l1l1l_m6ai_ (u"ࠨࡅ࡯ࡥࡸࡹࠧࣝ"): [l1l1l_m6ai_ (u"ࠩ࡜ࡩࡸ࠭ࣞ"), l1l1l_m6ai_ (u"ࠪࡒࡴ࠭ࣟ"), l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨ࣠"), l1l1l_m6ai_ (u"ࠬࡔ࡯ࠨ࣡"), l1l1l_m6ai_ (u"࡙࠭ࡦࡵࠪ࣢"), l1l1l_m6ai_ (u"ࠧࡏࡱࣣࠪ")]
        })
        l1ll1_m6ai_ = [l1l1l_m6ai_ (u"ࠨࡈࡨࡥࡹࡻࡲࡦ࠳ࠪࣤ"), l1l1l_m6ai_ (u"ࠩࡉࡩࡦࡺࡵࡳࡧ࠵ࠫࣥ")]
        l1111_m6ai_ = self.l111lll_m6ai_(l1lll_m6ai_, l1l1l_m6ai_ (u"ࠪࡇࡱࡧࡳࡴࣦࠩ"), l1ll1_m6ai_)
        l11l1_m6ai_ = function(l1lll_m6ai_, l1l1l_m6ai_ (u"ࠫࡈࡲࡡࡴࡵࠪࣧ"), l1ll1_m6ai_)
        if not isinstance(l11l1_m6ai_, str):
            raise ValueError(
                l1l1l_m6ai_ (u"࡚ࠧࡨࡦࠢࡩࡹࡳࡩࡴࡪࡱࡱࠤࡸ࡮࡯ࡶ࡮ࡧࠤࡷ࡫ࡴࡶࡴࡱࠤࡦࠦࡳࡵࡴ࡬ࡲ࡬࠲ࠠࡣࡷࡷࠤࡷ࡫ࡴࡶࡴࡱࡩࡩࠦࠢࣨ") + type(l11l1_m6ai_).__name__ + l1l1l_m6ai_ (u"ࠨ࠮ࣩࠣ")
            )
        if l11l1_m6ai_ != l1111_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠢࡕࡧࡶࡸࠥࡩࡡࡴࡧࠣ࠵ࠥ࡬ࡡࡪ࡮ࡨࡨ࠿ࠦࡅࡹࡲࡨࡧࡹ࡫ࡤࠡࡨࡨࡥࡹࡻࡲࡦࠢࡷࡳࠥࡹࡰ࡭࡫ࡷࠤࡴࡴࠠࠣ࣪") + l1111_m6ai_ + l1l1l_m6ai_ (u"ࠣ࠮ࠣࡦࡺࡺࠠࡨࡱࡷࠤࠧ࣫") + l11l1_m6ai_ + l1l1l_m6ai_ (u"ࠤ࠱ࠤࠧ࣬"),
                l1l1l_m6ai_ (u"ࠥࡔࡱ࡫ࡡࡴࡧࠣࡩࡳࡹࡵࡳࡧࠣࡸ࡭ࡧࡴࠡࡶ࡫ࡩࠥ࡬ࡵ࡯ࡥࡷ࡭ࡴࡴࠠࡤࡱࡵࡶࡪࡩࡴ࡭ࡻࠣ࡭ࡩ࡫࡮ࡵ࡫ࡩ࡭ࡪࡹࠠࡵࡪࡨࠤ࡫࡫ࡡࡵࡷࡵࡩࠥࡽࡩࡵࡪࠣࡸ࡭࡫ࠠࡩ࡫ࡪ࡬ࡪࡹࡴࠡ࡫ࡱࡪࡴࡸ࡭ࡢࡶ࡬ࡳࡳࠦࡧࡢ࡫ࡱ࠲࣭ࠧ")
            )
        l1l1_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠫࡋ࡫ࡡࡵࡷࡵࡩ࠶࣮࠭"): [l1l1l_m6ai_ (u"ࠬࡇ࣯ࠧ"), l1l1l_m6ai_ (u"࠭ࡁࠨࣰ"), l1l1l_m6ai_ (u"ࠧࡃࣱࠩ"), l1l1l_m6ai_ (u"ࠨࡄࣲࠪ"), l1l1l_m6ai_ (u"ࠩࡄࠫࣳ"), l1l1l_m6ai_ (u"ࠪࡆࠬࣴ"), l1l1l_m6ai_ (u"ࠫࡈ࠭ࣵ"), l1l1l_m6ai_ (u"ࠬࡉࣶࠧ"), l1l1l_m6ai_ (u"࠭ࡃࠨࣷ")],
            l1l1l_m6ai_ (u"ࠧࡇࡧࡤࡸࡺࡸࡥ࠳ࠩࣸ"): [l1l1l_m6ai_ (u"ࠨ࡚ࣹࠪ"), l1l1l_m6ai_ (u"ࠩ࡜ࣺࠫ"), l1l1l_m6ai_ (u"ࠪ࡜ࠬࣻ"), l1l1l_m6ai_ (u"ࠫ࡞࠭ࣼ"), l1l1l_m6ai_ (u"ࠬ࡞ࠧࣽ"), l1l1l_m6ai_ (u"࡙࠭ࠨࣾ"), l1l1l_m6ai_ (u"࡙ࠧࠩࣿ"), l1l1l_m6ai_ (u"ࠨ࡛ࠪऀ"), l1l1l_m6ai_ (u"ࠩ࡜ࠫँ")],
            l1l1l_m6ai_ (u"ࠪࡇࡱࡧࡳࡴࠩं"): [l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨः"), l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩऄ"), l1l1l_m6ai_ (u"࠭ࡎࡰࠩअ"), l1l1l_m6ai_ (u"ࠧࡏࡱࠪआ"), l1l1l_m6ai_ (u"ࠨ࡛ࡨࡷࠬइ"), l1l1l_m6ai_ (u"ࠩ࡜ࡩࡸ࠭ई"), l1l1l_m6ai_ (u"ࠪࡒࡴ࠭उ"), l1l1l_m6ai_ (u"ࠫࡓࡵࠧऊ"), l1l1l_m6ai_ (u"ࠬࡔ࡯ࠨऋ")]
        })
        l1ll1_m6ai_ = [l1l1l_m6ai_ (u"࠭ࡆࡦࡣࡷࡹࡷ࡫࠱ࠨऌ"), l1l1l_m6ai_ (u"ࠧࡇࡧࡤࡸࡺࡸࡥ࠳ࠩऍ")]
        l1111_m6ai_ = self.l111lll_m6ai_(l1l1_m6ai_, l1l1l_m6ai_ (u"ࠨࡅ࡯ࡥࡸࡹࠧऎ"), l1ll1_m6ai_)
        l11l1_m6ai_ = function(l1l1_m6ai_, l1l1l_m6ai_ (u"ࠩࡆࡰࡦࡹࡳࠨए"), l1ll1_m6ai_)
        if l11l1_m6ai_ != l1111_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠥࡘࡪࡹࡴࠡࡥࡤࡷࡪࠦ࠲ࠡࡨࡤ࡭ࡱ࡫ࡤ࠻ࠢࡈࡼࡵ࡫ࡣࡵࡧࡧࠤ࡫࡫ࡡࡵࡷࡵࡩࠥࡺ࡯ࠡࡵࡳࡰ࡮ࡺࠠࡰࡰࠣࠦऐ") + l1111_m6ai_ + l1l1l_m6ai_ (u"ࠦ࠱ࠦࡢࡶࡶࠣ࡫ࡴࡺࠠࠣऑ") + l11l1_m6ai_ + l1l1l_m6ai_ (u"ࠧ࠴ࠠࠣऒ"),
                l1l1l_m6ai_ (u"ࠨࡐ࡭ࡧࡤࡷࡪࠦࡥ࡯ࡵࡸࡶࡪࠦࡴࡩࡣࡷࠤࡹ࡮ࡥࠡࡨࡸࡲࡨࡺࡩࡰࡰࠣ࡬ࡦࡴࡤ࡭ࡧࡶࠤࡺࡴࡥࡷࡧࡱࠤࡨࡲࡡࡴࡵࠣࡨ࡮ࡹࡴࡳ࡫ࡥࡹࡹ࡯࡯࡯ࡵࠣࡧࡴࡸࡲࡦࡥࡷࡰࡾ࠴ࠢओ")
            )
        l11ll1_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠧࡇࡧࡤࡸࡺࡸࡥ࠲ࠩऔ"): [l1l1l_m6ai_ (u"ࠨࡃࠪक"), l1l1l_m6ai_ (u"ࠩࡅࠫख"), l1l1l_m6ai_ (u"ࠪࡇࠬग"), l1l1l_m6ai_ (u"ࠫࡆ࠭घ"), l1l1l_m6ai_ (u"ࠬࡈࠧङ"), l1l1l_m6ai_ (u"࠭ࡃࠨच"), l1l1l_m6ai_ (u"ࠧࡅࠩछ"), l1l1l_m6ai_ (u"ࠨࡆࠪज"), l1l1l_m6ai_ (u"ࠩࡇࠫझ")],
            l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠶ࠬञ"): [l1l1l_m6ai_ (u"ࠫ࡝࠭ट"), l1l1l_m6ai_ (u"ࠬ࡟ࠧठ"), l1l1l_m6ai_ (u"࠭ࡘࠨड"), l1l1l_m6ai_ (u"࡚ࠧࠩढ"), l1l1l_m6ai_ (u"ࠨ࡚ࠪण"), l1l1l_m6ai_ (u"ࠩ࡜ࠫत"), l1l1l_m6ai_ (u"ࠪ࡜ࠬथ"), l1l1l_m6ai_ (u"ࠫ࡞࠭द"), l1l1l_m6ai_ (u"ࠬ࡞ࠧध")],
            l1l1l_m6ai_ (u"࠭ࡃ࡭ࡣࡶࡷࠬन"): [l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫऩ"), l1l1l_m6ai_ (u"ࠨࡐࡲࠫप"), l1l1l_m6ai_ (u"ࠩࡐࡥࡾࡨࡥࠨफ"), l1l1l_m6ai_ (u"ࠪ࡝ࡪࡹࠧब"), l1l1l_m6ai_ (u"ࠫࡓࡵࠧभ"), l1l1l_m6ai_ (u"ࠬࡓࡡࡺࡤࡨࠫम"), l1l1l_m6ai_ (u"࡙࠭ࡦࡵࠪय"), l1l1l_m6ai_ (u"ࠧࡎࡣࡼࡦࡪ࠭र"), l1l1l_m6ai_ (u"ࠨࡏࡤࡽࡧ࡫ࠧऱ")]
        })
        l1ll1_m6ai_ = [l1l1l_m6ai_ (u"ࠩࡉࡩࡦࡺࡵࡳࡧ࠴ࠫल"), l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠶ࠬळ")]
        l1111_m6ai_ = self.l111lll_m6ai_(l11ll1_m6ai_, l1l1l_m6ai_ (u"ࠫࡈࡲࡡࡴࡵࠪऴ"), l1ll1_m6ai_)
        l11l1_m6ai_ = function(l11ll1_m6ai_, l1l1l_m6ai_ (u"ࠬࡉ࡬ࡢࡵࡶࠫव"), l1ll1_m6ai_)
        if l11l1_m6ai_ != l1111_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠨࡔࡦࡵࡷࠤࡨࡧࡳࡦࠢ࠶ࠤ࡫ࡧࡩ࡭ࡧࡧ࠾ࠥࡋࡸࡱࡧࡦࡸࡪࡪࠠࡧࡧࡤࡸࡺࡸࡥࠡࡶࡲࠤࡸࡶ࡬ࡪࡶࠣࡳࡳࠦࠢश") + l1111_m6ai_ + l1l1l_m6ai_ (u"ࠢ࠭ࠢࡥࡹࡹࠦࡧࡰࡶࠣࠦष") + l11l1_m6ai_ + l1l1l_m6ai_ (u"ࠣ࠰ࠣࠦस"),
                l1l1l_m6ai_ (u"ࠤࡓࡰࡪࡧࡳࡦࠢࡨࡲࡸࡻࡲࡦࠢࡷ࡬ࡦࡺࠠࡵࡪࡨࠤ࡫ࡻ࡮ࡤࡶ࡬ࡳࡳࠦࡣࡰࡴࡵࡩࡨࡺ࡬ࡺࠢ࡫ࡥࡳࡪ࡬ࡦࡵࠣࡱࡺࡲࡴࡪࡲ࡯ࡩࠥࡩ࡬ࡢࡵࡶࡩࡸࠦࡩ࡯ࠢࡷ࡬ࡪࠦࡦࡦࡣࡷࡹࡷ࡫࠮ࠣह")
            )
        l1l1111_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬऺ"): [l1l1l_m6ai_ (u"ࠫࡆ࠭ऻ"), l1l1l_m6ai_ (u"ࠬࡇ़ࠧ"), l1l1l_m6ai_ (u"࠭ࡂࠨऽ"), l1l1l_m6ai_ (u"ࠧࡃࠩा"), l1l1l_m6ai_ (u"ࠨࡅࠪि"), l1l1l_m6ai_ (u"ࠩࡆࠫी")],
            l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠶ࠬु"): [l1l1l_m6ai_ (u"ࠫ࡝࠭ू"), l1l1l_m6ai_ (u"ࠬ࡞ࠧृ"), l1l1l_m6ai_ (u"࡙࠭ࠨॄ"), l1l1l_m6ai_ (u"࡚ࠧࠩॅ"), l1l1l_m6ai_ (u"ࠨ࡜ࠪॆ"), l1l1l_m6ai_ (u"ࠩ࡝ࠫे")],
            l1l1l_m6ai_ (u"ࠪࡇࡱࡧࡳࡴࠩै"): [l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨॉ"), l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩॊ"), l1l1l_m6ai_ (u"࠭ࡎࡰࠩो"), l1l1l_m6ai_ (u"ࠧࡏࡱࠪौ"), l1l1l_m6ai_ (u"ࠨࡏࡤࡽࡧ࡫्ࠧ"), l1l1l_m6ai_ (u"ࠩࡐࡥࡾࡨࡥࠨॎ")]
        })
        l1ll1_m6ai_ = [l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬॏ"), l1l1l_m6ai_ (u"ࠫࡋ࡫ࡡࡵࡷࡵࡩ࠷࠭ॐ")]
        l1111_m6ai_ = self.l111lll_m6ai_(l1l1111_m6ai_, l1l1l_m6ai_ (u"ࠬࡉ࡬ࡢࡵࡶࠫ॑"), l1ll1_m6ai_)
        l11l1_m6ai_ = function(l1l1111_m6ai_, l1l1l_m6ai_ (u"࠭ࡃ࡭ࡣࡶࡷ॒ࠬ"), l1ll1_m6ai_)
        if l11l1_m6ai_ != l1111_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠢࡕࡧࡶࡸࠥࡩࡡࡴࡧࠣ࠸ࠥ࡬ࡡࡪ࡮ࡨࡨ࠿ࠦࡅࡹࡲࡨࡧࡹ࡫ࡤࠡࡨࡨࡥࡹࡻࡲࡦࠢࡷࡳࠥࡹࡰ࡭࡫ࡷࠤࡴࡴࠠࠣ॓") + l1111_m6ai_ + l1l1l_m6ai_ (u"ࠣ࠮ࠣࡦࡺࡺࠠࡨࡱࡷࠤࠧ॔") + l11l1_m6ai_ + l1l1l_m6ai_ (u"ࠤ࠱ࠤࠧॕ"),
                l1l1l_m6ai_ (u"ࠥࡘ࡭࡫ࠠࡧࡷࡱࡧࡹ࡯࡯࡯ࠢࡶ࡬ࡴࡻ࡬ࡥࠢࡦࡳࡷࡸࡥࡤࡶ࡯ࡽࠥ࡯ࡤࡦࡰࡷ࡭࡫ࡿࠠࡵࡪࡨࠤ࡫࡫ࡡࡵࡷࡵࡩࠥࡽࡩࡵࡪࠣࡸ࡭࡫ࠠࡩ࡫ࡪ࡬ࡪࡹࡴࠡ࡫ࡱࡪࡴࡸ࡭ࡢࡶ࡬ࡳࡳࠦࡧࡢ࡫ࡱࠤࡼ࡮ࡥ࡯ࠢࡷ࡬ࡪࠦࡦࡦࡣࡷࡹࡷ࡫ࠠࡱࡧࡵࡪࡪࡩࡴ࡭ࡻࠣࡷࡪࡶࡡࡳࡣࡷࡩࡸࠦࡴࡩࡧࠣࡧࡱࡧࡳࡴࡧࡶ࠲ࠧॖ")
            )
        l1l111l_m6ai_ = pd.read_csv(l1l1l_m6ai_ (u"ࠦࡩࡧࡴࡢࡵࡨࡸࡤࡏࡔࡠࡲࡵࡳ࡯࡫ࡣࡵࡡࡶࡹࡨࡩࡥࡴࡵ࠱ࡧࡸࡼࠢॗ"), skipinitialspace=True)
        l1ll1_m6ai_ = [l1l1l_m6ai_ (u"࡚ࠬࡥࡤࡪࡱࡳࡱࡵࡧࡪࡥࡤࡰࠥࡉ࡯࡮ࡲ࡯ࡩࡽ࡯ࡴࡺࠩक़"), l1l1l_m6ai_ (u"࠭ࡓࡵࡣࡩࡪࠥࡋࡸࡱࡧࡵࡸ࡮ࡹࡥࠨख़"), l1l1l_m6ai_ (u"ࠧࡑࡴࡲ࡮ࡪࡩࡴࠡࡕ࡬ࡾࡪ࠭ग़"),
                    l1l1l_m6ai_ (u"ࠨࡔࡨࡵࡺ࡯ࡲࡦ࡯ࡨࡲࡹࡹࠠࡒࡷࡤࡰ࡮ࡺࡹࠨज़"), l1l1l_m6ai_ (u"ࠩࡖࡸࡦࡱࡥࡩࡱ࡯ࡨࡪࡸࠠࡎࡣࡱࡥ࡬࡫࡭ࡦࡰࡷࠫड़"), l1l1l_m6ai_ (u"ࠪࡑࡦࡸ࡫ࡦࡶࠣࡇࡴࡴࡤࡪࡶ࡬ࡳࡳࡹࠧढ़"),
                    l1l1l_m6ai_ (u"ࠫࡕࡸ࡯࡫ࡧࡦࡸࠥࡓࡡ࡯ࡣࡪࡩࡲ࡫࡮ࡵࠢࡔࡹࡦࡲࡩࡵࡻࠪफ़")]
        l1111_m6ai_ = self.l111lll_m6ai_(l1l111l_m6ai_, l1l1l_m6ai_ (u"ࠬࡖࡲࡰ࡬ࡨࡧࡹࠦࡓࡶࡥࡦࡩࡸࡹࠧय़"), l1ll1_m6ai_)
        l11l1_m6ai_ = function(l1l111l_m6ai_, l1l1l_m6ai_ (u"࠭ࡐࡳࡱ࡭ࡩࡨࡺࠠࡔࡷࡦࡧࡪࡹࡳࠨॠ"), l1ll1_m6ai_)
        if l11l1_m6ai_ != l1111_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠢࡕࡧࡶࡸࠥࡩࡡࡴࡧࠣ࠹ࠥ࡬ࡡࡪ࡮ࡨࡨ࠿ࠦࡅࡹࡲࡨࡧࡹ࡫ࡤࠡࡨࡨࡥࡹࡻࡲࡦࠢࡷࡳࠥࡹࡰ࡭࡫ࡷࠤࡴࡴࠠࠣॡ") + l1111_m6ai_ + l1l1l_m6ai_ (u"ࠣ࠮ࠣࡦࡺࡺࠠࡨࡱࡷࠤࠧॢ") + l11l1_m6ai_ + l1l1l_m6ai_ (u"ࠤ࠱ࠤࠧॣ"),
                l1l1l_m6ai_ (u"ࠥࡘ࡭࡫ࠠࡧࡷࡱࡧࡹ࡯࡯࡯ࠢࡶ࡬ࡴࡻ࡬ࡥࠢࡦࡳࡷࡸࡥࡤࡶ࡯ࡽࠥ࡯ࡤࡦࡰࡷ࡭࡫ࡿࠠࡵࡪࡨࠤ࡫࡫ࡡࡵࡷࡵࡩࠥࡽࡩࡵࡪࠣࡸ࡭࡫ࠠࡩ࡫ࡪ࡬ࡪࡹࡴࠡ࡫ࡱࡪࡴࡸ࡭ࡢࡶ࡬ࡳࡳࠦࡧࡢ࡫ࡱࠤ࡫ࡵࡲࠡࡶ࡫ࡩࠥࡸࡥࡢ࡮ࠣࡨࡦࡺࡡࡴࡧࡷ࠲ࠧ।")
            )
    def test_split_dataset(self, function):
        l1lll_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠫࡋ࡫ࡡࡵࡷࡵࡩ࠶࠭॥"): [l1l1l_m6ai_ (u"ࠬࡇࠧ०"), l1l1l_m6ai_ (u"࠭ࡁࠨ१"), l1l1l_m6ai_ (u"ࠧࡃࠩ२"), l1l1l_m6ai_ (u"ࠨࡄࠪ३"), l1l1l_m6ai_ (u"ࠩࡆࠫ४"), l1l1l_m6ai_ (u"ࠪࡇࠬ५")],
            l1l1l_m6ai_ (u"ࠫࡋ࡫ࡡࡵࡷࡵࡩ࠷࠭६"): [l1l1l_m6ai_ (u"ࠬ࡞ࠧ७"), l1l1l_m6ai_ (u"࡙࠭ࠨ८"), l1l1l_m6ai_ (u"࡙ࠧࠩ९"), l1l1l_m6ai_ (u"ࠨ࡛ࠪ॰"), l1l1l_m6ai_ (u"࡛ࠩࠫॱ"), l1l1l_m6ai_ (u"ࠪ࡝ࠬॲ")],
            l1l1l_m6ai_ (u"ࠫࡈࡲࡡࡴࡵࠪॳ"): [l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩॴ"), l1l1l_m6ai_ (u"࠭ࡎࡰࠩॵ"), l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫॶ"), l1l1l_m6ai_ (u"ࠨࡐࡲࠫॷ"), l1l1l_m6ai_ (u"ࠩ࡜ࡩࡸ࠭ॸ"), l1l1l_m6ai_ (u"ࠪࡒࡴ࠭ॹ")]
        })
        feature = l1l1l_m6ai_ (u"ࠫࡋ࡫ࡡࡵࡷࡵࡩ࠶࠭ॺ")
        l11llll_m6ai_ = [
            l1lll_m6ai_[l1lll_m6ai_[feature] == l1l1l_m6ai_ (u"ࠬࡇࠧॻ")],
            l1lll_m6ai_[l1lll_m6ai_[feature] == l1l1l_m6ai_ (u"࠭ࡂࠨॼ")],
            l1lll_m6ai_[l1lll_m6ai_[feature] == l1l1l_m6ai_ (u"ࠧࡄࠩॽ")]
        ]
        l1111l_m6ai_ = function(l1lll_m6ai_, feature)
        if not isinstance(l1111l_m6ai_, list):
            raise ValueError(
                l1l1l_m6ai_ (u"ࠣࡖ࡫ࡩࠥ࡬ࡵ࡯ࡥࡷ࡭ࡴࡴࠠࡴࡪࡲࡹࡱࡪࠠࡳࡧࡷࡹࡷࡴࠠࡢࠢ࡯࡭ࡸࡺࠠࡰࡨࠣࡈࡦࡺࡡࡇࡴࡤࡱࡪࡹࠬࠡࡤࡸࡸࠥࡸࡥࡵࡷࡵࡲࡪࡪࠠࠣॾ") + type(l1111l_m6ai_).__name__ + l1l1l_m6ai_ (u"ࠤ࠱ࠦॿ")
            )
        if len(l1111l_m6ai_) != len(l11llll_m6ai_):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠥࡘࡪࡹࡴࠡࡥࡤࡷࡪࠦ࠱ࠡࡨࡤ࡭ࡱ࡫ࡤ࠻ࠢࡈࡼࡵ࡫ࡣࡵࡧࡧࠤࠧঀ") + str(len(l11llll_m6ai_)) + l1l1l_m6ai_ (u"ࠦࠥࡹࡰ࡭࡫ࡷࡷ࠱ࠦࡢࡶࡶࠣ࡫ࡴࡺࠠࠣঁ") + str(len(l1111l_m6ai_)) + l1l1l_m6ai_ (u"ࠧ࠴ࠢং")
            )
        for i, (expected, l1l1ll_m6ai_) in enumerate(zip(l11llll_m6ai_, l1111l_m6ai_)):
            if not expected.equals(l1l1ll_m6ai_):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠨࡔࡦࡵࡷࠤࡨࡧࡳࡦࠢ࠴ࠤ࡫ࡧࡩ࡭ࡧࡧ࠾࡙ࠥࡰ࡭࡫ࡷࠤࠧঃ") + str(i + 1) + l1l1l_m6ai_ (u"ࠢࠡࡦࡲࡩࡸࠦ࡮ࡰࡶࠣࡱࡦࡺࡣࡩࠢࡷ࡬ࡪࠦࡥࡹࡲࡨࡧࡹ࡫ࡤࠡࡆࡤࡸࡦࡌࡲࡢ࡯ࡨ࠲ࡡࡴࠢ঄"),
                    l1l1l_m6ai_ (u"ࠣࡇࡻࡴࡪࡩࡴࡦࡦ࠽ࡠࡳࠨঅ") + str(expected) + l1l1l_m6ai_ (u"ࠤ࡟ࡲࡡࡴࡇࡰࡶ࠽ࡠࡳࠨআ") + str(l1l1ll_m6ai_)
                )
        l1l1_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬই"): [l1l1l_m6ai_ (u"ࠫࡆ࠭ঈ"), l1l1l_m6ai_ (u"ࠬࡈࠧউ"), l1l1l_m6ai_ (u"࠭ࡁࠨঊ"), l1l1l_m6ai_ (u"ࠧࡄࠩঋ"), l1l1l_m6ai_ (u"ࠨࡄࠪঌ"), l1l1l_m6ai_ (u"ࠩࡆࠫ঍"), l1l1l_m6ai_ (u"ࠪࡇࠬ঎")],
            l1l1l_m6ai_ (u"ࠫࡋ࡫ࡡࡵࡷࡵࡩ࠷࠭এ"): [l1l1l_m6ai_ (u"ࠬ࡞ࠧঐ"), l1l1l_m6ai_ (u"࠭ࡘࠨ঑"), l1l1l_m6ai_ (u"࡚ࠧࠩ঒"), l1l1l_m6ai_ (u"ࠨ࡚ࠪও"), l1l1l_m6ai_ (u"ࠩ࡜ࠫঔ"), l1l1l_m6ai_ (u"ࠪ࡜ࠬক"), l1l1l_m6ai_ (u"ࠫ࡞࠭খ")],
            l1l1l_m6ai_ (u"ࠬࡉ࡬ࡢࡵࡶࠫগ"): [l1l1l_m6ai_ (u"࡙࠭ࡦࡵࠪঘ"), l1l1l_m6ai_ (u"ࠧࡏࡱࠪঙ"), l1l1l_m6ai_ (u"ࠨ࡛ࡨࡷࠬচ"), l1l1l_m6ai_ (u"ࠩࡐࡥࡾࡨࡥࠨছ"), l1l1l_m6ai_ (u"ࠪࡒࡴ࠭জ"), l1l1l_m6ai_ (u"ࠫࡒࡧࡹࡣࡧࠪঝ"), l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩঞ")]
        })
        feature = l1l1l_m6ai_ (u"࠭ࡆࡦࡣࡷࡹࡷ࡫࠱ࠨট")
        l11llll_m6ai_ = [
            l1l1_m6ai_[l1l1_m6ai_[feature] == l1l1l_m6ai_ (u"ࠧࡂࠩঠ")],
            l1l1_m6ai_[l1l1_m6ai_[feature] == l1l1l_m6ai_ (u"ࠨࡄࠪড")],
            l1l1_m6ai_[l1l1_m6ai_[feature] == l1l1l_m6ai_ (u"ࠩࡆࠫঢ")]
        ]
        l1111l_m6ai_ = function(l1l1_m6ai_, feature)
        if len(l1111l_m6ai_) != len(l11llll_m6ai_):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠥࡘࡪࡹࡴࠡࡥࡤࡷࡪࠦ࠲ࠡࡨࡤ࡭ࡱ࡫ࡤ࠻ࠢࡈࡼࡵ࡫ࡣࡵࡧࡧࠤࠧণ") + str(len(l11llll_m6ai_)) + l1l1l_m6ai_ (u"ࠦࠥࡹࡰ࡭࡫ࡷࡷ࠱ࠦࡢࡶࡶࠣ࡫ࡴࡺࠠࠣত") + str(len(l1111l_m6ai_)) + l1l1l_m6ai_ (u"ࠧ࠴ࠢথ")
            )
        for i, (expected, l1l1ll_m6ai_) in enumerate(zip(l11llll_m6ai_, l1111l_m6ai_)):
            if not expected.equals(l1l1ll_m6ai_):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠨࡔࡦࡵࡷࠤࡨࡧࡳࡦࠢ࠵ࠤ࡫ࡧࡩ࡭ࡧࡧ࠾࡙ࠥࡰ࡭࡫ࡷࠤࠧদ") + str(i + 1) + l1l1l_m6ai_ (u"ࠢࠡࡦࡲࡩࡸࠦ࡮ࡰࡶࠣࡱࡦࡺࡣࡩࠢࡷ࡬ࡪࠦࡥࡹࡲࡨࡧࡹ࡫ࡤࠡࡆࡤࡸࡦࡌࡲࡢ࡯ࡨ࠲ࡡࡴࠢধ"),
                    l1l1l_m6ai_ (u"ࠣࡇࡻࡴࡪࡩࡴࡦࡦ࠽ࡠࡳࠨন") + str(expected) + l1l1l_m6ai_ (u"ࠤ࡟ࡲࡡࡴࡇࡰࡶ࠽ࡠࡳࠨ঩") + str(l1l1ll_m6ai_)
                )
        l11ll1_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠪࡊࡪࡧࡴࡶࡴࡨ࠵ࠬপ"): [l1l1l_m6ai_ (u"ࠫࡆ࠭ফ"), l1l1l_m6ai_ (u"ࠬࡈࠧব"), l1l1l_m6ai_ (u"࠭ࡃࠨভ"), l1l1l_m6ai_ (u"ࠧࡅࠩম"), l1l1l_m6ai_ (u"ࠨࡃࠪয"), l1l1l_m6ai_ (u"ࠩࡅࠫর"), l1l1l_m6ai_ (u"ࠪࡇࠬ঱"), l1l1l_m6ai_ (u"ࠫࡉ࠭ল")],
            l1l1l_m6ai_ (u"ࠬࡌࡥࡢࡶࡸࡶࡪ࠸ࠧ঳"): [l1l1l_m6ai_ (u"࠭ࡘࠨ঴"), l1l1l_m6ai_ (u"࡚ࠧࠩ঵"), l1l1l_m6ai_ (u"ࠨ࡚ࠪশ"), l1l1l_m6ai_ (u"ࠩ࡜ࠫষ"), l1l1l_m6ai_ (u"ࠪ࡜ࠬস"), l1l1l_m6ai_ (u"ࠫ࡞࠭হ"), l1l1l_m6ai_ (u"ࠬ࡞ࠧ঺"), l1l1l_m6ai_ (u"࡙࠭ࠨ঻")],
            l1l1l_m6ai_ (u"ࠧࡄ࡮ࡤࡷࡸ়࠭"): [l1l1l_m6ai_ (u"ࠨ࡛ࡨࡷࠬঽ"), l1l1l_m6ai_ (u"ࠩࡑࡳࠬা"), l1l1l_m6ai_ (u"ࠪࡑࡦࡿࡢࡦࠩি"), l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨী"), l1l1l_m6ai_ (u"ࠬࡔ࡯ࠨু"), l1l1l_m6ai_ (u"࠭ࡍࡢࡻࡥࡩࠬূ"), l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫৃ"), l1l1l_m6ai_ (u"ࠨࡐࡲࠫৄ")]
        })
        feature = l1l1l_m6ai_ (u"ࠩࡉࡩࡦࡺࡵࡳࡧ࠴ࠫ৅")
        l11llll_m6ai_ = [
            l11ll1_m6ai_[l11ll1_m6ai_[feature] == l1l1l_m6ai_ (u"ࠪࡅࠬ৆")],
            l11ll1_m6ai_[l11ll1_m6ai_[feature] == l1l1l_m6ai_ (u"ࠫࡇ࠭ে")],
            l11ll1_m6ai_[l11ll1_m6ai_[feature] == l1l1l_m6ai_ (u"ࠬࡉࠧৈ")],
            l11ll1_m6ai_[l11ll1_m6ai_[feature] == l1l1l_m6ai_ (u"࠭ࡄࠨ৉")]
        ]
        l1111l_m6ai_ = function(l11ll1_m6ai_, feature)
        if len(l1111l_m6ai_) != len(l11llll_m6ai_):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠢࡕࡧࡶࡸࠥࡩࡡࡴࡧࠣ࠷ࠥ࡬ࡡࡪ࡮ࡨࡨ࠿ࠦࡅࡹࡲࡨࡧࡹ࡫ࡤࠡࠤ৊") + str(len(l11llll_m6ai_)) + l1l1l_m6ai_ (u"ࠣࠢࡶࡴࡱ࡯ࡴࡴ࠮ࠣࡦࡺࡺࠠࡨࡱࡷࠤࠧো") + str(len(l1111l_m6ai_)) + l1l1l_m6ai_ (u"ࠤ࠱ࠦৌ")
            )
        for i, (expected, l1l1ll_m6ai_) in enumerate(zip(l11llll_m6ai_, l1111l_m6ai_)):
            if not expected.equals(l1l1ll_m6ai_):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠥࡘࡪࡹࡴࠡࡥࡤࡷࡪࠦ࠳ࠡࡨࡤ࡭ࡱ࡫ࡤ࠻ࠢࡖࡴࡱ࡯ࡴࠡࠤ্") + str(i + 1) + l1l1l_m6ai_ (u"ࠦࠥࡪ࡯ࡦࡵࠣࡲࡴࡺࠠ࡮ࡣࡷࡧ࡭ࠦࡴࡩࡧࠣࡩࡽࡶࡥࡤࡶࡨࡨࠥࡊࡡࡵࡣࡉࡶࡦࡳࡥ࠯࡞ࡱࠦৎ"),
                    l1l1l_m6ai_ (u"ࠧࡋࡸࡱࡧࡦࡸࡪࡪ࠺࡝ࡰࠥ৏") + str(expected) + l1l1l_m6ai_ (u"ࠨ࡜࡯࡞ࡱࡋࡴࡺ࠺࡝ࡰࠥ৐") + str(l1l1ll_m6ai_)
                )
        l111_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠧࡇࡧࡤࡸࡺࡸࡥ࠲ࠩ৑"): [l1l1l_m6ai_ (u"ࠨࡃࠪ৒"), l1l1l_m6ai_ (u"ࠩࡄࠫ৓"), l1l1l_m6ai_ (u"ࠪࡅࠬ৔"), l1l1l_m6ai_ (u"ࠫࡆ࠭৕")],
            l1l1l_m6ai_ (u"ࠬࡌࡥࡢࡶࡸࡶࡪ࠸ࠧ৖"): [l1l1l_m6ai_ (u"࠭ࡘࠨৗ"), l1l1l_m6ai_ (u"࡚ࠧࠩ৘"), l1l1l_m6ai_ (u"ࠨ࡚ࠪ৙"), l1l1l_m6ai_ (u"ࠩ࡜ࠫ৚")],
            l1l1l_m6ai_ (u"ࠪࡇࡱࡧࡳࡴࠩ৛"): [l1l1l_m6ai_ (u"ࠫ࡞࡫ࡳࠨড়"), l1l1l_m6ai_ (u"ࠬࡔ࡯ࠨঢ়"), l1l1l_m6ai_ (u"࡙࠭ࡦࡵࠪ৞"), l1l1l_m6ai_ (u"ࠧࡏࡱࠪয়")]
        })
        feature = l1l1l_m6ai_ (u"ࠨࡈࡨࡥࡹࡻࡲࡦ࠳ࠪৠ")
        l11llll_m6ai_ = [l111_m6ai_]
        l1111l_m6ai_ = function(l111_m6ai_, feature)
        if len(l1111l_m6ai_) != len(l11llll_m6ai_):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠤࡗࡩࡸࡺࠠࡤࡣࡶࡩࠥ࠺ࠠࡧࡣ࡬ࡰࡪࡪ࠺ࠡࡇࡻࡴࡪࡩࡴࡦࡦࠣࠦৡ") + str(len(l11llll_m6ai_)) + l1l1l_m6ai_ (u"ࠥࠤࡸࡶ࡬ࡪࡶ࠯ࠤࡧࡻࡴࠡࡩࡲࡸࠥࠨৢ") + str(len(l1111l_m6ai_)) + l1l1l_m6ai_ (u"ࠦ࠳ࠨৣ")
            )
        if not l11llll_m6ai_[0].equals(l1111l_m6ai_[0]):
            raise AssertionError(
                l1l1l_m6ai_ (u"࡚ࠧࡥࡴࡶࠣࡧࡦࡹࡥࠡ࠶ࠣࡪࡦ࡯࡬ࡦࡦ࠽ࠤ࡙࡮ࡥࠡࡵࡳࡰ࡮ࡺࠠࡥࡱࡨࡷࠥࡴ࡯ࡵࠢࡰࡥࡹࡩࡨࠡࡶ࡫ࡩࠥ࡫ࡸࡱࡧࡦࡸࡪࡪࠠࡅࡣࡷࡥࡋࡸࡡ࡮ࡧ࠱ࡠࡳࠨ৤"),
                l1l1l_m6ai_ (u"ࠨࡅࡹࡲࡨࡧࡹ࡫ࡤ࠻࡞ࡱࠦ৥") + str(l11llll_m6ai_[0]) + l1l1l_m6ai_ (u"ࠢ࡝ࡰ࡟ࡲࡌࡵࡴ࠻࡞ࡱࠦ০") + str(l1111l_m6ai_[0])
            )
        l1l111l_m6ai_ = pd.read_csv(l1l1l_m6ai_ (u"ࠣࡦࡤࡸࡦࡹࡥࡵࡡࡌࡘࡤࡶࡲࡰ࡬ࡨࡧࡹࡥࡳࡶࡥࡦࡩࡸࡹ࠮ࡤࡵࡹࠦ১"), skipinitialspace=True)
        feature = l1l1l_m6ai_ (u"ࠩࡕࡩࡶࡻࡩࡳࡧࡰࡩࡳࡺࡳࠡࡓࡸࡥࡱ࡯ࡴࡺࠩ২")
        l11llll_m6ai_ = [l1l111l_m6ai_[l1l111l_m6ai_[feature] == val] for val in l1l111l_m6ai_[feature].unique()]
        l1111l_m6ai_ = function(l1l111l_m6ai_, feature)
        if not isinstance(l1111l_m6ai_, list):
            raise ValueError(
                l1l1l_m6ai_ (u"ࠥࡘ࡭࡫ࠠࡧࡷࡱࡧࡹ࡯࡯࡯ࠢࡶ࡬ࡴࡻ࡬ࡥࠢࡵࡩࡹࡻࡲ࡯ࠢࡤࠤࡱ࡯ࡳࡵࠢࡲࡪࠥࡊࡡࡵࡣࡉࡶࡦࡳࡥࡴ࠮ࠣࡦࡺࡺࠠࡳࡧࡷࡹࡷࡴࡥࡥࠢࠥ৩") + type(l1111l_m6ai_).__name__ + l1l1l_m6ai_ (u"ࠦ࠳ࠨ৪")
            )
        l1ll1l_m6ai_ = len(l1l111l_m6ai_[feature].unique())
        if len(l1111l_m6ai_) != l1ll1l_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"࡚ࠧࡥࡴࡶࠣࡧࡦࡹࡥࠡ࠷ࠣࡪࡦ࡯࡬ࡦࡦ࠽ࠤࡊࡾࡰࡦࡥࡷࡩࡩࠦࠢ৫") + str(l1ll1l_m6ai_) + l1l1l_m6ai_ (u"ࠨࠠࡴࡲ࡯࡭ࡹࡹࠬࠡࡤࡸࡸࠥ࡭࡯ࡵࠢࠥ৬") + str(len(l1111l_m6ai_)) + l1l1l_m6ai_ (u"ࠢ࠯ࠤ৭")
            )
        for i, split in enumerate(l1111l_m6ai_):
            if not isinstance(split, pd.DataFrame):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠣࡖࡨࡷࡹࠦࡣࡢࡵࡨࠤ࠺ࠦࡦࡢ࡫࡯ࡩࡩࡀࠠࡔࡲ࡯࡭ࡹࠦࠢ৮") + str(i + 1) + l1l1l_m6ai_ (u"ࠤࠣࡷ࡭ࡵࡵ࡭ࡦࠣࡦࡪࠦࡡࠡࡲࡤࡲࡩࡧࡳࠡࡆࡤࡸࡦࡌࡲࡢ࡯ࡨ࠰ࠥࡨࡵࡵࠢࡪࡳࡹࠦࠢ৯") + type(split).__name__ + l1l1l_m6ai_ (u"ࠥ࠲ࠧৰ")
                )
        print(l1l1l_m6ai_ (u"࡙ࠦ࡫ࡳࡵࠢࡦࡥࡸ࡫ࠠ࠶࠼ࠣࡖࡪࡧ࡬ࠡࡦࡤࡸࡦࡹࡥࡵࠤৱ"))
        print(l1l1l_m6ai_ (u"ࠧࡔࡵ࡮ࡤࡨࡶࠥࡵࡦࠡࡵࡳࡰ࡮ࡺࡳ࠻ࠤ৲"), len(l1111l_m6ai_))
        print(l1l1l_m6ai_ (u"ࠨࡔࡺࡲࡨࠤࡴ࡬ࠠࡦࡣࡦ࡬ࠥࡹࡰ࡭࡫ࡷࠤ࡮ࡹࠢ৳"), type(l1111l_m6ai_[0]))
        print(l1l1l_m6ai_ (u"ࠢࡕࡪࡨࠤࡸࡶ࡬ࡪࡶࡶࠤࡦࡸࡥࠡࡵࡷࡳࡷ࡫ࡤࠡ࡫ࡱࠤࡦࡀࠢ৴"), type(l1111l_m6ai_))
        for i, (expected, l1l1ll_m6ai_) in enumerate(zip(l11llll_m6ai_, l1111l_m6ai_)):
            if not expected.equals(l1l1ll_m6ai_):
                raise AssertionError(
                    l1l1l_m6ai_ (u"ࠣࡖࡨࡷࡹࠦࡣࡢࡵࡨࠤ࠺ࠦࡦࡢ࡫࡯ࡩࡩࡀࠠࡔࡲ࡯࡭ࡹࠦࠢ৵") + str(i + 1) + l1l1l_m6ai_ (u"ࠤࠣࡨࡴ࡫ࡳࠡࡰࡲࡸࠥࡳࡡࡵࡥ࡫ࠤࡹ࡮ࡥࠡࡧࡻࡴࡪࡩࡴࡦࡦࠣࡈࡦࡺࡡࡇࡴࡤࡱࡪ࠴࡜࡯ࠤ৶"),
                    l1l1l_m6ai_ (u"ࠥࡉࡽࡶࡥࡤࡶࡨࡨ࠿ࡢ࡮ࠣ৷") + str(expected) + l1l1l_m6ai_ (u"ࠦࡡࡴ࡜࡯ࡉࡲࡸ࠿ࡢ࡮ࠣ৸") + str(l1l1ll_m6ai_)
                )
    def test_train_test_split(self, function):
        l1lll_m6ai_ = pd.DataFrame({
            l1l1l_m6ai_ (u"ࠬࡌࡥࡢࡶࡸࡶࡪ࠷ࠧ৹"): range(10),
            l1l1l_m6ai_ (u"࠭ࡆࡦࡣࡷࡹࡷ࡫࠲ࠨ৺"): range(10, 20),
            l1l1l_m6ai_ (u"ࠧࡄ࡮ࡤࡷࡸ࠭৻"): [l1l1l_m6ai_ (u"ࠨ࡛ࡨࡷࠬৼ"), l1l1l_m6ai_ (u"ࠩࡑࡳࠬ৽"), l1l1l_m6ai_ (u"ࠪ࡝ࡪࡹࠧ৾"), l1l1l_m6ai_ (u"ࠫࡓࡵࠧ৿"), l1l1l_m6ai_ (u"ࠬ࡟ࡥࡴࠩ਀"), l1l1l_m6ai_ (u"࠭ࡎࡰࠩਁ"), l1l1l_m6ai_ (u"࡚ࠧࡧࡶࠫਂ"), l1l1l_m6ai_ (u"ࠨࡐࡲࠫਃ"), l1l1l_m6ai_ (u"ࠩ࡜ࡩࡸ࠭਄"), l1l1l_m6ai_ (u"ࠪࡒࡴ࠭ਅ")]
        })
        ratio = 0.5
        l11ll11_m6ai_ = int((1 - ratio) * l1lll_m6ai_.shape[0])
        l1llll1_m6ai_ = l1lll_m6ai_.shape[0] - l11ll11_m6ai_
        l1ll_m6ai_, test = function(l1lll_m6ai_, ratio)
        if not isinstance(l1ll_m6ai_, pd.DataFrame) or not isinstance(test, pd.DataFrame):
            raise AssertionError(
                l1l1l_m6ai_ (u"࡙ࠦ࡫ࡳࡵࠢࡦࡥࡸ࡫ࠠ࠲ࠢࡩࡥ࡮ࡲࡥࡥ࠼ࠣࡆࡴࡺࡨࠡࡶࡵࡥ࡮ࡴࠠࡢࡰࡧࠤࡹ࡫ࡳࡵࠢࡶࡩࡹࡹࠠࡴࡪࡲࡹࡱࡪࠠࡣࡧࠣࡴࡦࡴࡤࡢࡵࠣࡈࡦࡺࡡࡇࡴࡤࡱࡪࡹ࠮ࠣਆ"),
                l1l1l_m6ai_ (u"ࠧࡍ࡯ࡵ࠼ࠣࡸࡷࡧࡩ࡯࠿ࠥਇ") + type(l1ll_m6ai_).__name__ + l1l1l_m6ai_ (u"ࠨࠬࠡࡶࡨࡷࡹࡃࠢਈ") + type(test).__name__
            )
        if l1ll_m6ai_.shape[0] != l11ll11_m6ai_ or test.shape[0] != l1llll1_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠢࡕࡧࡶࡸࠥࡩࡡࡴࡧࠣ࠵ࠥ࡬ࡡࡪ࡮ࡨࡨ࠿ࠦࡅࡹࡲࡨࡧࡹ࡫ࡤࠡࡶࡵࡥ࡮ࡴࠠࡴࡧࡷࠤࡼ࡯ࡴࡩࠢࠥਉ") + str(l11ll11_m6ai_) + l1l1l_m6ai_ (u"ࠣࠢࡵࡳࡼࡹࠠࡢࡰࡧࠤࡹ࡫ࡳࡵࠢࡶࡩࡹࠦࡷࡪࡶ࡫ࠤࠧਊ") + str(l1llll1_m6ai_) + l1l1l_m6ai_ (u"ࠤࠣࡶࡴࡽࡳ࠯ࠤ਋"),
                l1l1l_m6ai_ (u"ࠥࡋࡴࡺ࠺ࠡࡶࡵࡥ࡮ࡴ࠮ࡴࡪࡤࡴࡪࡃࠢ਌") + str(l1ll_m6ai_.shape) + l1l1l_m6ai_ (u"ࠦ࠱ࠦࡴࡦࡵࡷ࠲ࡸ࡮ࡡࡱࡧࡀࠦ਍") + str(test.shape)
            )
        ratio = 0.25
        l11ll11_m6ai_ = int((1 - ratio) * l1lll_m6ai_.shape[0])
        l1llll1_m6ai_ = l1lll_m6ai_.shape[0] - l11ll11_m6ai_
        l1ll_m6ai_, test = function(l1lll_m6ai_, ratio)
        if not isinstance(l1ll_m6ai_, pd.DataFrame) or not isinstance(test, pd.DataFrame):
            raise AssertionError(
                l1l1l_m6ai_ (u"࡚ࠧࡥࡴࡶࠣࡧࡦࡹࡥࠡ࠴ࠣࡪࡦ࡯࡬ࡦࡦ࠽ࠤࡇࡵࡴࡩࠢࡷࡶࡦ࡯࡮ࠡࡣࡱࡨࠥࡺࡥࡴࡶࠣࡷࡪࡺࡳࠡࡵ࡫ࡳࡺࡲࡤࠡࡤࡨࠤࡵࡧ࡮ࡥࡣࡶࠤࡉࡧࡴࡢࡈࡵࡥࡲ࡫ࡳ࠯ࠤ਎"),
                l1l1l_m6ai_ (u"ࠨࡇࡰࡶ࠽ࠤࡹࡸࡡࡪࡰࡀࠦਏ") + type(l1ll_m6ai_).__name__ + l1l1l_m6ai_ (u"ࠢ࠭ࠢࡷࡩࡸࡺ࠽ࠣਐ") + type(test).__name__
            )
        if l1ll_m6ai_.shape[0] != l11ll11_m6ai_ or test.shape[0] != l1llll1_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠣࡖࡨࡷࡹࠦࡣࡢࡵࡨࠤ࠷ࠦࡦࡢ࡫࡯ࡩࡩࡀࠠࡆࡺࡳࡩࡨࡺࡥࡥࠢࡷࡶࡦ࡯࡮ࠡࡵࡨࡸࠥࡽࡩࡵࡪࠣࠦ਑") + str(l11ll11_m6ai_) + l1l1l_m6ai_ (u"ࠤࠣࡶࡴࡽࡳࠡࡣࡱࡨࠥࡺࡥࡴࡶࠣࡷࡪࡺࠠࡸ࡫ࡷ࡬ࠥࠨ਒") + str(l1llll1_m6ai_) + l1l1l_m6ai_ (u"ࠥࠤࡷࡵࡷࡴ࠰ࠥਓ"),
                l1l1l_m6ai_ (u"ࠦࡌࡵࡴ࠻ࠢࡷࡶࡦ࡯࡮࠯ࡵ࡫ࡥࡵ࡫࠽ࠣਔ") + str(l1ll_m6ai_.shape) + l1l1l_m6ai_ (u"ࠧ࠲ࠠࡵࡧࡶࡸ࠳ࡹࡨࡢࡲࡨࡁࠧਕ") + str(test.shape)
            )
        l1l111l_m6ai_ = pd.read_csv(l1l1l_m6ai_ (u"ࠨࡤࡢࡶࡤࡷࡪࡺ࡟ࡊࡖࡢࡴࡷࡵࡪࡦࡥࡷࡣࡸࡻࡣࡤࡧࡶࡷ࠳ࡩࡳࡷࠤਖ"), skipinitialspace=True)
        ratio = 0.25
        l11ll11_m6ai_ = int((1 - ratio) * l1l111l_m6ai_.shape[0])
        l1llll1_m6ai_ = l1l111l_m6ai_.shape[0] - l11ll11_m6ai_
        l1ll_m6ai_, test = function(l1l111l_m6ai_, ratio)
        if not isinstance(l1ll_m6ai_, pd.DataFrame) or not isinstance(test, pd.DataFrame):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠢࡕࡧࡶࡸࠥࡩࡡࡴࡧࠣ࠷ࠥ࡬ࡡࡪ࡮ࡨࡨ࠿ࠦࡂࡰࡶ࡫ࠤࡹࡸࡡࡪࡰࠣࡥࡳࡪࠠࡵࡧࡶࡸࠥࡹࡥࡵࡵࠣࡷ࡭ࡵࡵ࡭ࡦࠣࡦࡪࠦࡰࡢࡰࡧࡥࡸࠦࡄࡢࡶࡤࡊࡷࡧ࡭ࡦࡵ࠱ࠦਗ"),
                l1l1l_m6ai_ (u"ࠣࡉࡲࡸ࠿ࠦࡴࡳࡣ࡬ࡲࡂࠨਘ") + type(l1ll_m6ai_).__name__ + l1l1l_m6ai_ (u"ࠤ࠯ࠤࡹ࡫ࡳࡵ࠿ࠥਙ") + type(test).__name__
            )
        if l1ll_m6ai_.shape[0] != l11ll11_m6ai_ or test.shape[0] != l1llll1_m6ai_:
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠥࡘࡪࡹࡴࠡࡥࡤࡷࡪࠦ࠳ࠡࡨࡤ࡭ࡱ࡫ࡤ࠻ࠢࡈࡼࡵ࡫ࡣࡵࡧࡧࠤࡹࡸࡡࡪࡰࠣࡷࡪࡺࠠࡸ࡫ࡷ࡬ࠥࠨਚ") + str(l11ll11_m6ai_) + l1l1l_m6ai_ (u"ࠦࠥࡸ࡯ࡸࡵࠣࡥࡳࡪࠠࡵࡧࡶࡸࠥࡹࡥࡵࠢࡺ࡭ࡹ࡮ࠠࠣਛ") + str(l1llll1_m6ai_) + l1l1l_m6ai_ (u"ࠧࠦࡲࡰࡹࡶ࠲ࠧਜ"),
                l1l1l_m6ai_ (u"ࠨࡇࡰࡶ࠽ࠤࡹࡸࡡࡪࡰ࠱ࡷ࡭ࡧࡰࡦ࠿ࠥਝ") + str(l1ll_m6ai_.shape) + l1l1l_m6ai_ (u"ࠢ࠭ࠢࡷࡩࡸࡺ࠮ࡴࡪࡤࡴࡪࡃࠢਞ") + str(test.shape)
            )
        print(l1l1l_m6ai_ (u"ࠣࡖࡨࡷࡹࠦࡣࡢࡵࡨࠤ࠸ࡀࠠࡓࡧࡤࡰࠥࡪࡡࡵࡣࡶࡩࡹࠦࡷࡪࡶ࡫ࠤ࠼࠻࠭࠳࠷ࠣࡷࡵࡲࡩࡵࠤਟ"))
        print(l1l1l_m6ai_ (u"ࠤࡷࡶࡦ࡯࡮࠯ࡵ࡫ࡥࡵ࡫࠺ࠣਠ"), l1ll_m6ai_.shape)
        print(l1l1l_m6ai_ (u"ࠥࡸࡪࡹࡴ࠯ࡵ࡫ࡥࡵ࡫࠺ࠣਡ"), test.shape)
        print(l1l1l_m6ai_ (u"࡙ࠦࡸࡡࡪࡰࠣࡸࡾࡶࡥ࠻ࠤਢ"), type(l1ll_m6ai_))
        print(l1l1l_m6ai_ (u"࡚ࠧࡥࡴࡶࠣࡸࡾࡶࡥ࠻ࠤਣ"), type(test))
        if not test.head(5).equals(
                l1l111l_m6ai_.iloc[l11ll11_m6ai_:l11ll11_m6ai_ + 5].reset_index(drop=True)):
            raise AssertionError(
                l1l1l_m6ai_ (u"ࠨࡔࡦࡵࡷࠤࡨࡧࡳࡦࠢ࠶ࠤ࡫ࡧࡩ࡭ࡧࡧ࠾࡚ࠥࡨࡦࠢࡩ࡭ࡷࡹࡴࠡ࠷ࠣࡶࡴࡽࡳࠡࡱࡩࠤࡹ࡮ࡥࠡࡶࡨࡷࡹࠦࡳࡦࡶࠣࡨࡴࠦ࡮ࡰࡶࠣࡱࡦࡺࡣࡩࠢࡷ࡬ࡪࠦࡥࡹࡲࡨࡧࡹ࡫ࡤࠡࡸࡤࡰࡺ࡫ࡳ࠯࡞ࡱࠦਤ") +
                l1l1l_m6ai_ (u"ࠢࡆࡺࡳࡩࡨࡺࡥࡥ࠼࡟ࡲࠧਥ") + str(
                    l1l111l_m6ai_.iloc[l11ll11_m6ai_:l11ll11_m6ai_ + 5].reset_index(drop=True)) +
                l1l1l_m6ai_ (u"ࠣ࡞ࡱࡠࡳࡍ࡯ࡵ࠼࡟ࡲࠧਦ") + str(test.head(5))
            )
    def test_calculate_precision_recall(self, function, l11l111_m6ai_, l11l1ll_m6ai_, l11l1l_m6ai_=l1l1l_m6ai_ (u"ࠩࡉࡥ࡮ࡲࡵࡳࡧࠪਧ")):
        try:
            l1l111_m6ai_, precision = function(l11l111_m6ai_, l11l1ll_m6ai_, l11l1l_m6ai_)
        except Exception as e:
            raise ValueError(l1l1l_m6ai_ (u"ࠥࡉࡷࡸ࡯ࡳࠢࡨࡼࡪࡩࡵࡵ࡫ࡱ࡫ࠥࡩࡡ࡭ࡥࡸࡰࡦࡺࡥࡠࡲࡵࡩࡨ࡯ࡳࡪࡱࡱࡣࡷ࡫ࡣࡢ࡮࡯ࠤ࡫ࡻ࡮ࡤࡶ࡬ࡳࡳࡀࠠࠣਨ") + str(e))
        if not isinstance(l1l111_m6ai_, float) or not isinstance(precision, float):
            raise ValueError(l1l1l_m6ai_ (u"࡙ࠦ࡮ࡥࠡࡨࡸࡲࡨࡺࡩࡰࡰࠣࡷ࡭ࡵࡵ࡭ࡦࠣࡶࡪࡺࡵࡳࡰࠣࡶࡪࡩࡡ࡭࡮ࠣࡥࡳࡪࠠࡱࡴࡨࡧ࡮ࡹࡩࡰࡰࠣࡥࡸࠦࡦ࡭ࡱࡤࡸࡸ࠴ࠢ਩"))
        l111ll_m6ai_ = 0.8444444444444444
        l1l11l_m6ai_ = 0.7808219178082192
        if not np.isclose(l1l111_m6ai_, l111ll_m6ai_, atol=5e-2):
            raise ValueError(
                l1l1l_m6ai_ (u"ࠧࡘࡥࡤࡣ࡯ࡰࠥ࡬࡯ࡳࠢࡦࡰࡦࡹࡳࠡࠩࠥਪ") + str(l11l1l_m6ai_) + l1l1l_m6ai_ (u"ࠨࠧࠡ࡫ࡶࠤ࡮ࡴࡣࡰࡴࡵࡩࡨࡺ࠮ࠡࡇࡻࡴࡪࡩࡴࡦࡦ࠽ࠤࠧਫ") + str(
                    l111ll_m6ai_) + l1l1l_m6ai_ (u"ࠢ࠭ࠢࡥࡹࡹࠦࡧࡰࡶ࠽ࠤࠧਬ") + str(l1l111_m6ai_))
        if not np.isclose(precision, l1l11l_m6ai_, atol=5e-2):
            raise ValueError(
                l1l1l_m6ai_ (u"ࠣࡒࡵࡩࡨ࡯ࡳࡪࡱࡱࠤ࡫ࡵࡲࠡࡥ࡯ࡥࡸࡹࠠࠨࠤਭ") + str(l11l1l_m6ai_) + l1l1l_m6ai_ (u"ࠤࠪࠤ࡮ࡹࠠࡪࡰࡦࡳࡷࡸࡥࡤࡶ࠱ࠤࡊࡾࡰࡦࡥࡷࡩࡩࡀࠠࠣਮ") + str(
                    l1l11l_m6ai_) + l1l1l_m6ai_ (u"ࠥ࠰ࠥࡨࡵࡵࠢࡪࡳࡹࡀࠠࠣਯ") + str(precision))
    def test_create_sklearn_tree(self, function, dataset):
        try:
            l11lll1_m6ai_, accuracy, l1l111_m6ai_, precision, l11111_m6ai_ = function(dataset)
        except Exception as e:
            raise ValueError(l1l1l_m6ai_ (u"ࠦࡊࡸࡲࡰࡴࠣࡩࡽ࡫ࡣࡶࡶ࡬ࡲ࡬ࠦࡣࡳࡧࡤࡸࡪࡥࡳ࡬࡮ࡨࡥࡷࡴ࡟ࡵࡴࡨࡩࠥ࡬ࡵ࡯ࡥࡷ࡭ࡴࡴ࠺ࠡࠤਰ") + str(e))
        if not all(isinstance(metric, float) for metric in [accuracy, l1l111_m6ai_, precision]):
            raise ValueError(l1l1l_m6ai_ (u"࡚ࠧࡨࡦࠢࡩࡹࡳࡩࡴࡪࡱࡱࠤࡸ࡮࡯ࡶ࡮ࡧࠤࡷ࡫ࡴࡶࡴࡱࠤࡦࡩࡣࡶࡴࡤࡧࡾ࠲ࠠࡳࡧࡦࡥࡱࡲࠬࠡࡣࡱࡨࠥࡶࡲࡦࡥ࡬ࡷ࡮ࡵ࡮ࠡࡣࡶࠤ࡫ࡲ࡯ࡢࡶࡶ࠲ࠧ਱"))
        if not isinstance(l11111_m6ai_, np.ndarray) or l11111_m6ai_.shape != (2, 2):
            raise ValueError(l1l1l_m6ai_ (u"ࠨࡔࡩࡧࠣࡧࡴࡴࡦࡶࡵ࡬ࡳࡳࠦ࡭ࡢࡶࡵ࡭ࡽࠦࡳࡩࡱࡸࡰࡩࠦࡢࡦࠢࡤࠤ࠷ࡾ࠲ࠡࡰࡸࡱࡵࡿࠠࡢࡴࡵࡥࡾ࠴ࠢਲ"))
        if not (50 <= accuracy <= 100):
            raise ValueError(
                l1l1l_m6ai_ (u"ࠢࡂࡥࡦࡹࡷࡧࡣࡺࠢࡹࡥࡱࡻࡥࠡ࡫ࡶࠤࡴࡻࡴࠡࡱࡩࠤࡹ࡮ࡥࠡࡧࡻࡴࡪࡩࡴࡦࡦࠣࡶࡦࡴࡧࡦࠢ࡞࠹࠵ࠫࠬࠡ࠳࠳࠴ࠪࡣ࠮ࠡࡉࡲࡸ࠿ࠦࠢਲ਼") + str(round(accuracy, 2)) + l1l1l_m6ai_ (u"ࠣࠧࠥ਴"))
        if not (0 <= l1l111_m6ai_ <= 1):
            raise ValueError(l1l1l_m6ai_ (u"ࠤࡕࡩࡨࡧ࡬࡭ࠢࡹࡥࡱࡻࡥࠡ࡫ࡶࠤࡴࡻࡴࠡࡱࡩࠤࡹ࡮ࡥࠡࡸࡤࡰ࡮ࡪࠠࡳࡣࡱ࡫ࡪ࡛ࠦ࠱࠮ࠣ࠵ࡢ࠴ࠠࡈࡱࡷ࠾ࠥࠨਵ") + str(round(l1l111_m6ai_, 4)))
        if not (0 <= precision <= 1):
            raise ValueError(l1l1l_m6ai_ (u"ࠥࡔࡷ࡫ࡣࡪࡵ࡬ࡳࡳࠦࡶࡢ࡮ࡸࡩࠥ࡯ࡳࠡࡱࡸࡸࠥࡵࡦࠡࡶ࡫ࡩࠥࡼࡡ࡭࡫ࡧࠤࡷࡧ࡮ࡨࡧࠣ࡟࠵࠲ࠠ࠲࡟࠱ࠤࡌࡵࡴ࠻ࠢࠥਸ਼") + str(round(precision, 4)))
        if not isinstance(l11lll1_m6ai_, tree.ll_m6ai_):
            raise ValueError(l1l1l_m6ai_ (u"࡙ࠦ࡮ࡥࠡࡥࡵࡩࡦࡺࡥࡥࠢࡷࡶࡪ࡫ࠠࡴࡪࡲࡹࡱࡪࠠࡣࡧࠣࡥࡳࠦࡩ࡯ࡵࡷࡥࡳࡩࡥࠡࡱࡩࠤࡸࡱ࡬ࡦࡣࡵࡲ࠳ࡺࡲࡦࡧ࠱ࡈࡪࡩࡩࡴ࡫ࡲࡲ࡙ࡸࡥࡦࡅ࡯ࡥࡸࡹࡩࡧ࡫ࡨࡶ࠳ࠨ਷"))
        if l11lll1_m6ai_.l1ll111_m6ai_() > 3:
            raise ValueError(l1l1l_m6ai_ (u"࡚ࠧࡨࡦࠢࡷࡶࡪ࡫ࠠࡥࡧࡳࡸ࡭ࠦࡥࡹࡥࡨࡩࡩࡹࠠࡵࡪࡨࠤࡸࡶࡥࡤ࡫ࡩ࡭ࡪࡪࠠ࡮ࡣࡻ࡭ࡲࡻ࡭ࠡࡦࡨࡴࡹ࡮ࠠࡰࡨࠣ࠷࠳ࠨਸ"))
        print(l1l1l_m6ai_ (u"ࠨࡔࡦࡵࡷࠤࡵࡧࡳࡴࡧࡧࠤࡼ࡯ࡴࡩ࠼ࠥਹ"))
        print(l1l1l_m6ai_ (u"ࠢࡂࡥࡦࡹࡷࡧࡣࡺ࠼ࠣࠦ਺") + str(round(accuracy, 2)) + l1l1l_m6ai_ (u"ࠣࠧࠥ਻"))
        print(l1l1l_m6ai_ (u"ࠤࡕࡩࡨࡧ࡬࡭࠼਼ࠣࠦ") + str(round(l1l111_m6ai_, 4)))
        print(l1l1l_m6ai_ (u"ࠥࡔࡷ࡫ࡣࡪࡵ࡬ࡳࡳࡀࠠࠣ਽") + str(round(precision, 4)))
        print(l1l1l_m6ai_ (u"ࠦࡈࡵ࡮ࡧࡷࡶ࡭ࡴࡴࠠࡎࡣࡷࡶ࡮ࡾ࠺࡝ࡰࠥਾ") + str(l11111_m6ai_))