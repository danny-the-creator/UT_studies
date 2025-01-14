# coding: UTF-8
import sys
l1l11l_m6ai_ = sys.version_info [0] == 2
l111lll_m6ai_ = 2048
l111ll1_m6ai_ = 7
def l1ll1l_m6ai_ (l1l11l1_m6ai_):
    global l1l111_m6ai_
    ll_m6ai_ = ord (l1l11l1_m6ai_ [-1])
    l111l1_m6ai_ = l1l11l1_m6ai_ [:-1]
    l1l111l_m6ai_ = ll_m6ai_ % len (l111l1_m6ai_)
    l11111_m6ai_ = l111l1_m6ai_ [:l1l111l_m6ai_] + l111l1_m6ai_ [l1l111l_m6ai_:]
    if l1l11l_m6ai_:
        l11l1ll_m6ai_ = unicode () .join ([l111l11_m6ai_ (ord (char) - l111lll_m6ai_ - (l11ll11_m6ai_ + ll_m6ai_) % l111ll1_m6ai_) for l11ll11_m6ai_, char in enumerate (l11111_m6ai_)])
    else:
        l11l1ll_m6ai_ = str () .join ([chr (ord (char) - l111lll_m6ai_ - (l11ll11_m6ai_ + ll_m6ai_) % l111ll1_m6ai_) for l11ll11_m6ai_, char in enumerate (l11111_m6ai_)])
    return eval (l11l1ll_m6ai_)
import numpy as np
from sklearn import datasets
class Assignment:
    def __init__(self):
        self.l1l1lll_m6ai_ = datasets.load_iris()
        self.gamma = 1
        self.l111_m6ai_ = -0.04
        self.width = 4
        self.height = 3
        self.l1lllll_m6ai_ = [(1, 1)]
        self.l1l1l1_m6ai_ = [(3, 0), (3, 1)]
        self.l1111l_m6ai_ = [1, -1]
        self.l11ll_m6ai_ = self.l111ll_m6ai_(self.l111_m6ai_)
    def test_visualize_pca_iris(self, function, X, y):
        try:
            l1l1ll1_m6ai_, l1ll111_m6ai_ = function(X, y)
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠦࡊࡸࡲࡰࡴࠣࡩࡽ࡫ࡣࡶࡶ࡬ࡲ࡬ࠦࡶࡪࡵࡸࡥࡱ࡯ࡺࡦࡡࡳࡧࡦࡥࡩࡳ࡫ࡶࠤ࡫ࡻ࡮ࡤࡶ࡬ࡳࡳࡀࠠࠣࠀ") + str(e))
        if l1l1ll1_m6ai_.shape[1] != 2:
            raise ValueError(l1ll1l_m6ai_ (u"ࠧ࠸ࡄࠡࡒࡆࡅࠥࡸࡥࡴࡷ࡯ࡸࠥࡹࡨࡰࡷ࡯ࡨࠥ࡮ࡡࡷࡧࠣ࠶ࠥࡩ࡯࡮ࡲࡲࡲࡪࡴࡴࡴ࠰ࠣࡋࡴࡺ࠺ࠡࠤࠁ") + str(l1l1ll1_m6ai_.shape[1]))
        if l1ll111_m6ai_.shape[1] != 3:
            raise ValueError(l1ll1l_m6ai_ (u"ࠨ࠳ࡅࠢࡓࡇࡆࠦࡲࡦࡵࡸࡰࡹࠦࡳࡩࡱࡸࡰࡩࠦࡨࡢࡸࡨࠤ࠸ࠦࡣࡰ࡯ࡳࡳࡳ࡫࡮ࡵࡵ࠱ࠤࡌࡵࡴ࠻ࠢࠥࠂ") + str(l1ll111_m6ai_.shape[1]))
        if l1l1ll1_m6ai_.shape[0] != X.shape[0] or l1ll111_m6ai_.shape[0] != X.shape[0]:
            raise ValueError(l1ll1l_m6ai_ (u"ࠢࡕࡪࡨࠤࡳࡻ࡭ࡣࡧࡵࠤࡴ࡬ࠠࡴࡣࡰࡴࡱ࡫ࡳࠡ࡫ࡱࠤࡹ࡮ࡥࠡࡴࡨࡨࡺࡩࡥࡥࠢࡧࡥࡹࡧࠠࡥࡱࡨࡷࠥࡴ࡯ࡵࠢࡰࡥࡹࡩࡨࠡࡶ࡫ࡩࠥࡵࡲࡪࡩ࡬ࡲࡦࡲࠠࡥࡣࡷࡥ࠳ࠨࠃ"))
    def test_visualize_dendrogram_iris(self, function, X):
        try:
            l1l11ll_m6ai_, l11l_m6ai_ = function(X)
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠣࡇࡵࡶࡴࡸࠠࡦࡺࡨࡧࡺࡺࡩ࡯ࡩࠣࡺ࡮ࡹࡵࡢ࡮࡬ࡾࡪࡥࡤࡦࡰࡧࡶࡴ࡭ࡲࡢ࡯ࡢ࡭ࡷ࡯ࡳࠡࡨࡸࡲࡨࡺࡩࡰࡰ࠽ࠤࠧࠄ") + str(e))
        n_samples = X.shape[0]
        if l1l11ll_m6ai_.shape != (n_samples - 1, 4):
            raise ValueError(
                l1ll1l_m6ai_ (u"ࠤ࡚ࡥࡷࡪࠠ࡭࡫ࡱ࡯ࡦ࡭ࡥࠡࡦࡤࡸࡦࠦࡳࡩࡱࡸࡰࡩࠦࡨࡢࡸࡨࠤࡸ࡮ࡡࡱࡧࠣࠬࠧࠅ") + str(n_samples - 1) + l1ll1l_m6ai_ (u"ࠥ࠰ࠥ࠺ࠩ࠯ࠢࡊࡳࡹࡀࠠࠣࠆ") + str(
                    l1l11ll_m6ai_.shape))
        if l11l_m6ai_.shape != (n_samples - 1, 4):
            raise ValueError(
                l1ll1l_m6ai_ (u"ࠦࡈ࡫࡮ࡵࡴࡲ࡭ࡩࠦ࡬ࡪࡰ࡮ࡥ࡬࡫ࠠࡥࡣࡷࡥࠥࡹࡨࡰࡷ࡯ࡨࠥ࡮ࡡࡷࡧࠣࡷ࡭ࡧࡰࡦࠢࠫࠦࠇ") + str(n_samples - 1) + l1ll1l_m6ai_ (u"ࠧ࠲ࠠ࠵ࠫ࠱ࠤࡌࡵࡴ࠻ࠢࠥࠈ") + str(
                    l11l_m6ai_.shape))
        if l1l11ll_m6ai_[0, 2] < 0 or l11l_m6ai_[0, 2] < 0:
            raise ValueError(l1ll1l_m6ai_ (u"ࠨࡄࡪࡵࡷࡥࡳࡩࡥࠡ࡯ࡨࡸࡷ࡯ࡣࠡ࡯ࡸࡷࡹࠦࡢࡦࠢࡱࡳࡳ࠳࡮ࡦࡩࡤࡸ࡮ࡼࡥ࠭ࠢࡤࡲࡩࠦࡳࡩࡱࡸࡰࡩࠦࡵࡴࡧࠣࠫࡪࡻࡣ࡭࡫ࡧࡩࡦࡴࠧ࠯ࠤࠉ"))
    def test_perform_agglomerative_clustering(self, function, X):
        try:
            l11l1l1_m6ai_, l1ll11l_m6ai_ = function(X)
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠢࡆࡴࡵࡳࡷࠦࡥࡹࡧࡦࡹࡹ࡯࡮ࡨࠢࡳࡩࡷ࡬࡯ࡳ࡯ࡢࡥ࡬࡭࡬ࡰ࡯ࡨࡶࡦࡺࡩࡷࡧࡢࡧࡱࡻࡳࡵࡧࡵ࡭ࡳ࡭ࠠࡧࡷࡱࡧࡹ࡯࡯࡯࠼ࠣࠦࠊ") + str(e))
        if len(l11l1l1_m6ai_) != X.shape[0]:
            raise ValueError(
                l1ll1l_m6ai_ (u"ࠣࡏࡲࡨࡪࡲࠠ࠲࠼ࠣࡒࡺࡳࡢࡦࡴࠣࡳ࡫ࠦࡰࡳࡧࡧ࡭ࡨࡺࡩࡰࡰࡶࠤ࠭ࠨࠋ") + str(len(l11l1l1_m6ai_)) +
                l1ll1l_m6ai_ (u"ࠤࠬࠤࡩࡵࡥࡴࠢࡱࡳࡹࠦ࡭ࡢࡶࡦ࡬ࠥࡴࡵ࡮ࡤࡨࡶࠥࡵࡦࠡࡵࡤࡱࡵࡲࡥࡴࠢࠫࠦࠌ") + str(X.shape[0]) + l1ll1l_m6ai_ (u"ࠥ࠭࠳ࠨࠍ"))
        if len(l1ll11l_m6ai_) != X.shape[0]:
            raise ValueError(
                l1ll1l_m6ai_ (u"ࠦࡒࡵࡤࡦ࡮ࠣ࠶࠿ࠦࡎࡶ࡯ࡥࡩࡷࠦ࡯ࡧࠢࡳࡶࡪࡪࡩࡤࡶ࡬ࡳࡳࡹࠠࠩࠤࠎ") + str(len(l1ll11l_m6ai_)) +
                l1ll1l_m6ai_ (u"ࠧ࠯ࠠࡥࡱࡨࡷࠥࡴ࡯ࡵࠢࡰࡥࡹࡩࡨࠡࡰࡸࡱࡧ࡫ࡲࠡࡱࡩࠤࡸࡧ࡭ࡱ࡮ࡨࡷࠥ࠮ࠢࠏ") + str(X.shape[0]) + l1ll1l_m6ai_ (u"ࠨࠩ࠯ࠤࠐ"))
        if len(np.unique(l11l1l1_m6ai_)) != 3:
            raise ValueError(
                l1ll1l_m6ai_ (u"ࠢࡎࡱࡧࡩࡱࠦ࠱࠻ࠢࡈࡼࡵ࡫ࡣࡵࡧࡧࠤ࠸ࠦࡣ࡭ࡷࡶࡸࡪࡸࡳ࠭ࠢࡥࡹࡹࠦࡧࡰࡶࠣࠦࠑ") + str(len(np.unique(l11l1l1_m6ai_))) + l1ll1l_m6ai_ (u"ࠣࠢࡦࡰࡺࡹࡴࡦࡴࡶ࠲ࠧࠒ"))
    def test_evaluate_clusters_silhouette(self, function, X, l11l1l1_m6ai_, l1ll11l_m6ai_, l11l1l_m6ai_=3,
                                          l1111ll_m6ai_=2):
        try:
            l1l1l1l_m6ai_, l11lll_m6ai_ = function(X, l11l1l1_m6ai_, l1ll11l_m6ai_, l11l1l_m6ai_, l1111ll_m6ai_)
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠤࡈࡶࡷࡵࡲࠡࡧࡻࡩࡨࡻࡴࡪࡰࡪࠤࡪࡼࡡ࡭ࡷࡤࡸࡪࡥࡣ࡭ࡷࡶࡸࡪࡸࡳࡠࡵ࡬ࡰ࡭ࡵࡵࡦࡶࡷࡩࠥ࡬ࡵ࡯ࡥࡷ࡭ࡴࡴ࠺ࠡࠤࠓ") + str(e))
        if not isinstance(l1l1l1l_m6ai_, float) or not isinstance(l11lll_m6ai_, float):
            raise ValueError(l1ll1l_m6ai_ (u"ࠥࡘ࡭࡫ࠠࡧࡷࡱࡧࡹ࡯࡯࡯ࠢࡶ࡬ࡴࡻ࡬ࡥࠢࡵࡩࡹࡻࡲ࡯ࠢࡶ࡭ࡱ࡮࡯ࡶࡧࡷࡸࡪࠦࡳࡤࡱࡵࡩࡸࠦࡡࡴࠢࡩࡰࡴࡧࡴࡴ࠰ࠥࠔ"))
        if not (-1 <= l1l1l1l_m6ai_ <= 1):
            raise ValueError(l1ll1l_m6ai_ (u"ࠦࡘ࡯࡬ࡩࡱࡸࡩࡹࡺࡥࠡࡵࡦࡳࡷ࡫ࠠ࠲ࠢ࡬ࡷࠥࡵࡵࡵࠢࡲࡪࠥࡺࡨࡦࠢࡹࡥࡱ࡯ࡤࠡࡴࡤࡲ࡬࡫ࠠ࡜࠯࠴࠰ࠥ࠷࡝࠯ࠢࡊࡳࡹࡀࠠࠣࠕ") + str(l1l1l1l_m6ai_))
        if not (-1 <= l11lll_m6ai_ <= 1):
            raise ValueError(l1ll1l_m6ai_ (u"࡙ࠧࡩ࡭ࡪࡲࡹࡪࡺࡴࡦࠢࡶࡧࡴࡸࡥࠡ࠴ࠣ࡭ࡸࠦ࡯ࡶࡶࠣࡳ࡫ࠦࡴࡩࡧࠣࡺࡦࡲࡩࡥࠢࡵࡥࡳ࡭ࡥࠡ࡝࠰࠵࠱ࠦ࠱࡞࠰ࠣࡋࡴࡺ࠺ࠡࠤࠖ") + str(l11lll_m6ai_))
    def test_compute_confusion_matrix(self, function, l1_m6ai_, l11l1l1_m6ai_, l1ll11l_m6ai_):
        try:
            l1llll1_m6ai_, l11_m6ai_ = function(l1_m6ai_, l11l1l1_m6ai_, l1ll11l_m6ai_)
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠨࡅࡳࡴࡲࡶࠥ࡫ࡸࡦࡥࡸࡸ࡮ࡴࡧࠡࡥࡲࡱࡵࡻࡴࡦࡡࡦࡳࡳ࡬ࡵࡴ࡫ࡲࡲࡤࡳࡡࡵࡴ࡬ࡼࠥ࡬ࡵ࡯ࡥࡷ࡭ࡴࡴ࠺ࠡࠤࠗ") + str(e))
        if not isinstance(l1llll1_m6ai_, np.ndarray) or not isinstance(l11_m6ai_, np.ndarray):
            raise ValueError(l1ll1l_m6ai_ (u"ࠢࡕࡪࡨࠤ࡫ࡻ࡮ࡤࡶ࡬ࡳࡳࠦࡳࡩࡱࡸࡰࡩࠦࡲࡦࡶࡸࡶࡳࠦࡣࡰࡰࡩࡹࡸ࡯࡯࡯ࠢࡰࡥࡹࡸࡩࡤࡧࡶࠤࡦࡹࠠ࡯ࡷࡰࡴࡾࠦࡡࡳࡴࡤࡽࡸ࠴ࠢ࠘"))
        l1lll1l_m6ai_ = len(np.unique(l1_m6ai_))
        if l1llll1_m6ai_.shape != (l1lll1l_m6ai_, l1lll1l_m6ai_):
            raise ValueError(
                l1ll1l_m6ai_ (u"ࠣࡅࡲࡲ࡫ࡻࡳࡪࡱࡱࠤࡒࡧࡴࡳ࡫ࡻࠤ࠶ࠦࡨࡢࡵࠣ࡭ࡳࡩ࡯ࡳࡴࡨࡧࡹࠦࡳࡩࡣࡳࡩ࠳ࠦࡅࡹࡲࡨࡧࡹ࡫ࡤࠡࠪࠥ࠙") + str(l1lll1l_m6ai_) + l1ll1l_m6ai_ (u"ࠤ࠯ࠤࠧࠚ") + str(l1lll1l_m6ai_) +
                l1ll1l_m6ai_ (u"ࠥ࠭࠱ࠦࡧࡰࡶࠣࠦࠛ") + str(l1llll1_m6ai_.shape) + l1ll1l_m6ai_ (u"ࠦ࠳ࠨࠜ"))
        l1ll1l1_m6ai_ = len(np.unique(l1ll11l_m6ai_))
        if l11_m6ai_.shape != (l1ll1l1_m6ai_, l1ll1l1_m6ai_):
            raise ValueError(
                l1ll1l_m6ai_ (u"ࠧࡉ࡯࡯ࡨࡸࡷ࡮ࡵ࡮ࠡࡏࡤࡸࡷ࡯ࡸࠡ࠴ࠣ࡬ࡦࡹࠠࡪࡰࡦࡳࡷࡸࡥࡤࡶࠣࡷ࡭ࡧࡰࡦ࠰ࠣࡉࡽࡶࡥࡤࡶࡨࡨࠥ࠮ࠢࠝ") + str(l1ll1l1_m6ai_) + l1ll1l_m6ai_ (u"ࠨࠬࠡࠤࠞ") + str(l1ll1l1_m6ai_) +
                l1ll1l_m6ai_ (u"ࠢࠪ࠮ࠣ࡫ࡴࡺࠠࠣࠟ") + str(l11_m6ai_.shape) + l1ll1l_m6ai_ (u"ࠣ࠰ࠥࠠ"))
        if not np.issubdtype(l1llll1_m6ai_.dtype, np.integer) or np.any(l1llll1_m6ai_ < 0):
            raise ValueError(l1ll1l_m6ai_ (u"ࠤࡆࡳࡳ࡬ࡵࡴ࡫ࡲࡲࠥࡓࡡࡵࡴ࡬ࡼࠥ࠷ࠠࡤࡱࡱࡸࡦ࡯࡮ࡴࠢࡱࡳࡳ࠳ࡩ࡯ࡶࡨ࡫ࡪࡸࠠࡰࡴࠣࡲࡪ࡭ࡡࡵ࡫ࡹࡩࠥࡼࡡ࡭ࡷࡨࡷ࠳ࠨࠡ"))
        if not np.issubdtype(l11_m6ai_.dtype, np.integer) or np.any(l11_m6ai_ < 0):
            raise ValueError(l1ll1l_m6ai_ (u"ࠥࡇࡴࡴࡦࡶࡵ࡬ࡳࡳࠦࡍࡢࡶࡵ࡭ࡽࠦ࠲ࠡࡥࡲࡲࡹࡧࡩ࡯ࡵࠣࡲࡴࡴ࠭ࡪࡰࡷࡩ࡬࡫ࡲࠡࡱࡵࠤࡳ࡫ࡧࡢࡶ࡬ࡺࡪࠦࡶࡢ࡮ࡸࡩࡸ࠴ࠢࠢ"))
    def test_plot_clustering_results(self, function, l1l1ll1_m6ai_, y, l1ll11l_m6ai_):
        try:
            function(l1l1ll1_m6ai_, y, l1ll11l_m6ai_)
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠦࡊࡸࡲࡰࡴࠣࡩࡽ࡫ࡣࡶࡶ࡬ࡲ࡬ࠦࡰ࡭ࡱࡷࡣࡨࡲࡵࡴࡶࡨࡶ࡮ࡴࡧࡠࡴࡨࡷࡺࡲࡴࡴࠢࡩࡹࡳࡩࡴࡪࡱࡱ࠾ࠥࠨࠣ") + str(e))
    def l111ll_m6ai_(self,l111_m6ai_):
        l11ll_m6ai_ = np.zeros((self.width, self.height)) + l111_m6ai_
        for c, r in zip(self.l1l1l1_m6ai_, self.l1111l_m6ai_):
            l11ll_m6ai_[c] = r
        for c in self.l1lllll_m6ai_:
            l11ll_m6ai_[c] = 0
        return l11ll_m6ai_
    def valid(self, x, y):
        l1ll1l_m6ai_ (u"ࠧࠨࠢࡓࡧࡷࡹࡷࡴࠠࡸࡪࡨࡸ࡭࡫ࡲࠡࠪࡻ࠰ࡾ࠯ࠠࡪࡵࠣࡥࠥࡼࡡ࡭࡫ࡧࠤ࡬ࡸࡩࡥࠢࡳࡳࡸ࡯ࡴࡪࡱࡱࠦࠧࠨࠤ")
        return 0 <= x < self.width and 0 <= y < self.height and (x, y) not in self.l1lllll_m6ai_
    def l11ll1_m6ai_(self, x, y, a):
        l1ll1l_m6ai_ (u"ࠨࠢࠣࡆࡨࡸࡪࡸ࡭ࡪࡰࡨࠤࡹ࡮ࡥࠡࡴࡨࡷࡺࡲࡴࠡࡱࡩࠤࡦࡩࡴࡪࡱࡱࠤࡦࠦࡩ࡯ࠢࡦࡩࡱࡲࠠࠩࡺ࠯ࠤࡾ࠯ࠠࡪࡰࠣࡥࠥࡪࡥࡵࡧࡵࡱ࡮ࡴࡩࡴࡶ࡬ࡧࠥࡽ࡯ࡳ࡮ࡧࠦࠧࠨࠥ")
        if (x, y) in self.l1l1l1_m6ai_ or (x, y) in self.l1lllll_m6ai_:
            return self.l1lllll_m6ai_[0]
        cur = (x, y)
        if a == 0:
            y -= 1
        elif a == 1:
            x += 1
        elif a == 2:
            y += 1
        elif a == 3:
            x -= 1
        if self.valid(x, y):
            return (x, y)
        return cur
    def l1l1111_m6ai_(self, x, y, l1ll1_m6ai_):
        l1ll1l_m6ai_ (u"ࠢࠣࠤࡕࡩࡹࡻࡲ࡯ࠢࡷ࡬ࡪࠦࡢࡦࡵࡷࠤࡦࡩࡴࡪࡱࡱࠤࡼ࡫ࠠࡤࡣࡱࠤࡹࡧ࡫ࡦࠢ࡬ࡲࠥࡩࡥ࡭࡮ࠣࡼ࠱ࡿࠬࠡࡣࡱࡨࠥ࡯ࡴࡴࠢࡹࡥࡱࡻࡥࠣࠤࠥࠦ")
        if (x, y) in self.l1l1l1_m6ai_ or (x, y) in self.l1lllll_m6ai_:
            return -1, 0.0
        l1111_m6ai_ = -np.inf
        l1lll_m6ai_ = -1
        for a in range(4):
            v = 0.0
            xp, yp = self.l11ll1_m6ai_(x, y, a)
            v += 0.8 * l1ll1_m6ai_[xp, yp]
            xp, yp = self.l11ll1_m6ai_(x, y, (a - 1) % 4)
            v += 0.1 * l1ll1_m6ai_[xp, yp]
            xp, yp = self.l11ll1_m6ai_(x, y, (a + 1) % 4)
            v += 0.1 * l1ll1_m6ai_[xp, yp]
            if v >= l1111_m6ai_:
                l1111_m6ai_ = v
                l1lll_m6ai_ = a
        return l1lll_m6ai_, l1111_m6ai_
    def l1llll_m6ai_(self, l1ll1_m6ai_, l11ll_m6ai_, gamma):
        l1ll1l_m6ai_ (u"ࠣࠤࠥࡔࡪࡸࡦࡰࡴࡰࠤࡦࠦࡳࡪࡰࡪࡰࡪࠦࡩࡵࡧࡵࡥࡹ࡯࡯࡯ࠢࡲࡪࠥࡼࡡ࡭ࡷࡨࠤ࡮ࡺࡥࡳࡣࡷ࡭ࡴࡴࠠࡢ࡮ࡪࡳࡷ࡯ࡴࡩ࡯ࠥࠦࠧࠧ")
        ut = np.zeros(l1ll1_m6ai_.shape)
        l11ll1l_m6ai_ = np.zeros(l1ll1_m6ai_.shape, int) - 1
        for i in range(l1ll1_m6ai_.shape[0]):
            for j in range(l1ll1_m6ai_.shape[1]):
                a, v = self.l1l1111_m6ai_(i, j, l1ll1_m6ai_)
                ut[i, j] = l11ll_m6ai_[(i, j)] + gamma * v
                l11ll1l_m6ai_[i, j] = a
        return ut, l11ll1l_m6ai_
    def l11l111_m6ai_(self, l11ll1l_m6ai_):
        l1ll1l_m6ai_ (u"ࠤࠥࠦࡕࡸࡩ࡯ࡶࠣࡥࠥࡶ࡯࡭࡫ࡦࡽࠥࡺࡡࡣ࡮ࡨࠤ࡮ࡴࠠࡩࡷࡰࡥࡳ࠳ࡲࡦࡣࡧࡥࡧࡲࡥࠡࡨࡲࡶࡲࡧࡴࠣࠤࠥࠨ")
        l11l11_m6ai_ = [
            l1ll1l_m6ai_ (u"࡙ࠥࡵࠦࠠࠡࠢࠥࠩ"),
            l1ll1l_m6ai_ (u"ࠦࡗ࡯ࡧࡩࡶࠣࠦࠪ"),
            l1ll1l_m6ai_ (u"ࠧࡊ࡯ࡸࡰࠣࠤࠧࠫ"),
            l1ll1l_m6ai_ (u"ࠨࡌࡦࡨࡷࠤࠥࠨࠬ"),
            l1ll1l_m6ai_ (u"ࠢࠡࠢࠣࠤࠥࠦࠢ࠭"),
        ]
        for y in range(self.height):
            for x in range(self.width):
                print(l11l11_m6ai_[l11ll1l_m6ai_[x, y]], end=l1ll1l_m6ai_ (u"ࠣࠤ࠮"))
            print()
        print()
    def test_valueIteration(self, function, *args):
        l1ll1_m6ai_ = args[0]
        l1l_m6ai_, l1lll11_m6ai_ = self.l1llll_m6ai_(l1ll1_m6ai_, self.l11ll_m6ai_, self.gamma)
        try:
            l1l1l_m6ai_, l1lll1_m6ai_ = function(l1ll1_m6ai_, self.l11ll_m6ai_, self.gamma)
            if not np.allclose(l1l1l_m6ai_, l1l_m6ai_, atol=1e-4):
                raise ValueError(
                    l1ll1l_m6ai_ (u"ࠤࡘࡸ࡮ࡲࡩࡵࡻࠣࡸࡦࡨ࡬ࡦࠢ࡬ࡷࠥ࡯࡮ࡤࡱࡵࡶࡪࡩࡴ࠯࡞ࡱࡉࡽࡶࡥࡤࡶࡨࡨ࠿ࡢ࡮ࠣ࠯") + str(l1l_m6ai_) + l1ll1l_m6ai_ (u"ࠥࡠࡳࡍ࡯ࡵ࠼࡟ࡲࠧ࠰") + str(l1l1l_m6ai_))
            if not np.array_equal(l1lll1_m6ai_, l1lll11_m6ai_):
                raise ValueError(
                    l1ll1l_m6ai_ (u"ࠦࡕࡵ࡬ࡪࡥࡼࠤࡹࡧࡢ࡭ࡧࠣ࡭ࡸࠦࡩ࡯ࡥࡲࡶࡷ࡫ࡣࡵ࠰࡟ࡲࡊࡾࡰࡦࡥࡷࡩࡩࡀ࡜࡯ࠤ࠱") + str(l1lll11_m6ai_) + l1ll1l_m6ai_ (u"ࠧࡢ࡮ࡈࡱࡷ࠾ࡡࡴࠢ࠲") + str(l1lll1_m6ai_))
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠨࡅࡳࡴࡲࡶࠥ࡯࡮ࠡࡨࡸࡲࡨࡺࡩࡰࡰࠣࠫࡻࡧ࡬ࡶࡧࡌࡸࡪࡸࡡࡵ࡫ࡲࡲࠬࡀࠠ࡝ࡰ࡟ࡸࠧ࠳") + str(e))
    def iterate(self, l11ll_m6ai_, gamma):
        l1ll1_m6ai_ = np.zeros((self.width, self.height))
        delta = []
        while len(delta) < 5 or delta[-2] - delta[-1] > 0.0:
            l11llll_m6ai_, l11ll1l_m6ai_ = self.l1llll_m6ai_(l1ll1_m6ai_, l11ll_m6ai_, gamma)
            delta.append((l11llll_m6ai_ - l1ll1_m6ai_).max())
            l1ll1_m6ai_ = l11llll_m6ai_.copy()
        return delta, l1ll1_m6ai_, l11ll1l_m6ai_
    def l1l1l11_m6ai_(self):
        results = {}
        l1ll1ll_m6ai_ = [.01, .1, .5, .9, 1]
        for g in l1ll1ll_m6ai_:
            self.gamma = g
            self.l11ll_m6ai_ = self.l111ll_m6ai_(self.l111_m6ai_)
            delta, l1ll1_m6ai_, l11ll1l_m6ai_ = self.iterate(self.l11ll_m6ai_, self.gamma)
            results[g] = {
                l1ll1l_m6ai_ (u"ࠢࡥࡧ࡯ࡸࡦࠨ࠴"): delta,
                l1ll1l_m6ai_ (u"ࠣࡷࡷ࡭ࡱ࡯ࡴࡺࠤ࠵"): l1ll1_m6ai_,
                l1ll1l_m6ai_ (u"ࠤࡳࡳࡱ࡯ࡣࡺࠤ࠶"): l11ll1l_m6ai_,
            }
        return results
    def test_evaluate_gammas(self, function):
        l1ll_m6ai_ = self.l1l1l11_m6ai_()
        try:
            l11l1_m6ai_ = function()
            l1ll1ll_m6ai_ = [.01, .1, .5, .9, 1]
            for g in l1ll1ll_m6ai_:
                l11l11l_m6ai_ = l1ll_m6ai_[g]
                l1l11_m6ai_ = l11l1_m6ai_[g]
                if not np.allclose(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠥࡨࡪࡲࡴࡢࠤ࠷")], l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠦࡩ࡫࡬ࡵࡣࠥ࠸")], atol=1e-4):
                    raise ValueError(
                        l1ll1l_m6ai_ (u"ࠧࡊࡥ࡭ࡶࡤࠤࡻࡧ࡬ࡶࡧࡶࠤࡦࡸࡥࠡ࡫ࡱࡧࡴࡸࡲࡦࡥࡷࠤ࡫ࡵࡲࠡࡩࡤࡱࡲࡧ࠽ࠣ࠹") + str(g) + l1ll1l_m6ai_ (u"ࠨ࠮࡝ࡰࡈࡼࡵ࡫ࡣࡵࡧࡧ࠾ࡡࡴࠢ࠺") + str(
                            l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠢࡥࡧ࡯ࡸࡦࠨ࠻")]) +
                        l1ll1l_m6ai_ (u"ࠣ࡞ࡱࡋࡴࡺ࠺࡝ࡰࠥ࠼") + str(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠤࡧࡩࡱࡺࡡࠣ࠽")]))
                if not np.allclose(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠥࡹࡹ࡯࡬ࡪࡶࡼࠦ࠾")], l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠦࡺࡺࡩ࡭࡫ࡷࡽࠧ࠿")], atol=1e-4):
                    raise ValueError(
                        l1ll1l_m6ai_ (u"࡛ࠧࡴࡪ࡮࡬ࡸࡾࠦ࡭ࡢࡶࡵ࡭ࡽࠦࡩࡴࠢ࡬ࡲࡨࡵࡲࡳࡧࡦࡸࠥ࡬࡯ࡳࠢࡪࡥࡲࡳࡡ࠾ࠤࡀ") + str(g) + l1ll1l_m6ai_ (u"ࠨ࠮࡝ࡰࡈࡼࡵ࡫ࡣࡵࡧࡧ࠾ࡡࡴࠢࡁ") + str(
                            l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠢࡶࡶ࡬ࡰ࡮ࡺࡹࠣࡂ")]) +
                        l1ll1l_m6ai_ (u"ࠣ࡞ࡱࡋࡴࡺ࠺࡝ࡰࠥࡃ") + str(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠤࡸࡸ࡮ࡲࡩࡵࡻࠥࡄ")]))
                if not np.array_equal(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠥࡴࡴࡲࡩࡤࡻࠥࡅ")], l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠦࡵࡵ࡬ࡪࡥࡼࠦࡆ")]):
                    raise ValueError(
                        l1ll1l_m6ai_ (u"ࠧࡖ࡯࡭࡫ࡦࡽࠥࡳࡡࡵࡴ࡬ࡼࠥ࡯ࡳࠡ࡫ࡱࡧࡴࡸࡲࡦࡥࡷࠤ࡫ࡵࡲࠡࡩࡤࡱࡲࡧ࠽ࠣࡇ") + str(g) + l1ll1l_m6ai_ (u"ࠨ࠮࡝ࡰࡈࡼࡵ࡫ࡣࡵࡧࡧ࠾ࡡࡴࠢࡈ") + str(
                            l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠢࡱࡱ࡯࡭ࡨࡿࠢࡉ")]) +
                        l1ll1l_m6ai_ (u"ࠣ࡞ࡱࡋࡴࡺ࠺࡝ࡰࠥࡊ") + str(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠤࡳࡳࡱ࡯ࡣࡺࠤࡋ")]))
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠥࡉࡷࡸ࡯ࡳࠢ࡬ࡲࠥ࡬ࡵ࡯ࡥࡷ࡭ࡴࡴࠠࠨࡧࡹࡥࡱࡻࡡࡵࡧࡢ࡫ࡦࡳ࡭ࡢࡵࠪ࠾ࠥࡢ࡮࡝ࡶࠥࡌ") + str(e))
    def l111l1l_m6ai_(self):
        self.gamma = 1
        results = {}
        l1ll11_m6ai_ = [-2, -1, -0.4, -0.01, 1]
        for br in l1ll11_m6ai_:
            self.l11ll_m6ai_ = self.l111ll_m6ai_(br)
            delta, l1ll1_m6ai_, l11ll1l_m6ai_ = self.iterate(self.l11ll_m6ai_, self.gamma)
            results[br] = {
                l1ll1l_m6ai_ (u"ࠦࡩ࡫࡬ࡵࡣࠥࡍ"): delta,
                l1ll1l_m6ai_ (u"ࠧࡻࡴࡪ࡮࡬ࡸࡾࠨࡎ"): l1ll1_m6ai_,
                l1ll1l_m6ai_ (u"ࠨࡰࡰ࡮࡬ࡧࡾࠨࡏ"): l11ll1l_m6ai_,
            }
        return results
    def test_evaluate_policies_with_different_rewards(self, function):
        l1ll_m6ai_ = self.l111l1l_m6ai_()
        try:
            l11l1_m6ai_ = function()
            l1ll11_m6ai_ = [-2, -1, -0.4, -0.01, 1]
            for br in l1ll11_m6ai_:
                l11l11l_m6ai_ = l1ll_m6ai_[br]
                l1l11_m6ai_ = l11l1_m6ai_[br]
                l111l_m6ai_ = np.array(l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠧࡥࡧ࡯ࡸࡦ࠭ࡐ")])
                l1l1_m6ai_ = np.array(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠨࡦࡨࡰࡹࡧࠧࡑ")])
                print(l1ll1l_m6ai_ (u"ࠤࡅࡥࡨࡱࡧࡳࡱࡸࡲࡩࠦࡲࡦࡹࡤࡶࡩࡃࠢࡒ") + str(br) +
                      l1ll1l_m6ai_ (u"ࠥࠤࢁࠦࡃࡰࡴࡵࡩࡨࡺࠠࡥࡧ࡯ࡸࡦࠦࡳࡩࡣࡳࡩ࠿ࠦࠢࡓ") + str(l111l_m6ai_.shape) +
                      l1ll1l_m6ai_ (u"ࠦࠥࢂࠠࡔࡶࡸࡨࡪࡴࡴࠡࡦࡨࡰࡹࡧࠠࡴࡪࡤࡴࡪࡀࠠࠣࡔ") + str(l1l1_m6ai_.shape))
                if not np.allclose(l1l1_m6ai_, l111l_m6ai_, atol=1e-4):
                    raise ValueError(
                        l1ll1l_m6ai_ (u"ࠧࡊࡥ࡭ࡶࡤࠤࡻࡧ࡬ࡶࡧࡶࠤࡦࡸࡥࠡ࡫ࡱࡧࡴࡸࡲࡦࡥࡷࠤ࡫ࡵࡲࠡࡤࡤࡧࡰ࡭ࡲࡰࡷࡱࡨࠥࡸࡥࡸࡣࡵࡨࡂࠨࡕ") + str(br) +
                        l1ll1l_m6ai_ (u"ࠨ࠮࡝ࡰࡈࡼࡵ࡫ࡣࡵࡧࡧ࠾ࡡࡴࠢࡖ") + str(l111l_m6ai_) + l1ll1l_m6ai_ (u"ࠢ࡝ࡰࡊࡳࡹࡀ࡜࡯ࠤࡗ") + str(l1l1_m6ai_))
                if not np.allclose(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠣࡷࡷ࡭ࡱ࡯ࡴࡺࠤࡘ")], l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠤࡸࡸ࡮ࡲࡩࡵࡻ࡙ࠥ")], atol=1e-4):
                    raise ValueError(
                        l1ll1l_m6ai_ (u"࡙ࠥࡹ࡯࡬ࡪࡶࡼࠤࡲࡧࡴࡳ࡫ࡻࠤ࡮ࡹࠠࡪࡰࡦࡳࡷࡸࡥࡤࡶࠣࡪࡴࡸࠠࡣࡣࡦ࡯࡬ࡸ࡯ࡶࡰࡧࠤࡷ࡫ࡷࡢࡴࡧࡁ࡚ࠧ") + str(br) +
                        l1ll1l_m6ai_ (u"ࠦ࠳ࡢ࡮ࡆࡺࡳࡩࡨࡺࡥࡥ࠼࡟ࡲ࡛ࠧ") + str(l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠧࡻࡴࡪ࡮࡬ࡸࡾࠨ࡜")]) + l1ll1l_m6ai_ (u"ࠨ࡜࡯ࡉࡲࡸ࠿ࡢ࡮ࠣ࡝") + str(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠢࡶࡶ࡬ࡰ࡮ࡺࡹࠣ࡞")]))
                if not np.array_equal(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠣࡲࡲࡰ࡮ࡩࡹࠣ࡟")], l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠤࡳࡳࡱ࡯ࡣࡺࠤࡠ")]):
                    raise ValueError(
                        l1ll1l_m6ai_ (u"ࠥࡔࡴࡲࡩࡤࡻࠣࡱࡦࡺࡲࡪࡺࠣ࡭ࡸࠦࡩ࡯ࡥࡲࡶࡷ࡫ࡣࡵࠢࡩࡳࡷࠦࡢࡢࡥ࡮࡫ࡷࡵࡵ࡯ࡦࠣࡶࡪࡽࡡࡳࡦࡀࠦࡡ") + str(br) +
                        l1ll1l_m6ai_ (u"ࠦ࠳ࡢ࡮ࡆࡺࡳࡩࡨࡺࡥࡥ࠼࡟ࡲࠧࡢ") + str(l11l11l_m6ai_[l1ll1l_m6ai_ (u"ࠧࡶ࡯࡭࡫ࡦࡽࠧࡣ")]) + l1ll1l_m6ai_ (u"ࠨ࡜࡯ࡉࡲࡸ࠿ࡢ࡮ࠣࡤ") + str(l1l11_m6ai_[l1ll1l_m6ai_ (u"ࠢࡱࡱ࡯࡭ࡨࡿࠢࡥ")]))
        except Exception as e:
            raise ValueError(l1ll1l_m6ai_ (u"ࠣࡇࡵࡶࡴࡸࠠࡪࡰࠣࡪࡺࡴࡣࡵ࡫ࡲࡲࠥ࠭ࡥࡷࡣ࡯ࡹࡦࡺࡥࡠࡲࡲࡰ࡮ࡩࡩࡦࡵࡢࡻ࡮ࡺࡨࡠࡦ࡬ࡪ࡫࡫ࡲࡦࡰࡷࡣࡷ࡫ࡷࡢࡴࡧࡷࠬࡀࠠ࡝ࡰ࡟ࡸࠧࡦ") + str(e))