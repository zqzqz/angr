import logging
from collections import defaultdict

import networkx
import pyvex
from . import Analysis
from ..import global_apis


l = logging.getLogger(name=__name__)


class PointsTo(Analysis):
    def __init__(self):
        l.debug("Initializing Points-to Analysis")
        self._analyse()
        global_apis.POINTS_TO_ANALYSE=self
    
    def _analyse(self):
        l.debug("Doing Points-to Analysis")

    def get_points_to_set(self, ptr):
        return set([])

    def __repr__(self):
        return "This is the real points-to analyse"


from angr.analyses import AnalysesHub
AnalysesHub.register_default('PointsTo', PointsTo)
