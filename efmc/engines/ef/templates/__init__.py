# coding: utf-8
from .abstract_template import TemplateType, Template
from .interval import IntervalTemplate, DisjunctiveIntervalTemplate, IntervalTemplateV2
from .polyhedron import PolyTemplate, DisjunctivePolyTemplate
from .octagon import OctagonTemplate
from .zone import ZoneTemplate

from .bv_interval import BitVecIntervalTemplate, DisjunctiveBitVecIntervalTemplate
from .bv_zone import BitVecZoneTemplate, DisjunctiveBitVecZoneTemplate
from .bv_octagon import BitVecOctagonTemplate, DisjunctiveBitVecOctagonTemplate
from. bv_affine import BitVecAffineTemplate, DisjunctiveBitVecAffineTemplate
from .bv_polyhedron import BitVecPolyhedronTemplate, DisjunctiveBitVecPolyhedronTemplate


# Export (TODO: maybe export shorter names)
TemplateType = TemplateType
IntervalTemplate = IntervalTemplate
IntervalTemplateV2 = IntervalTemplateV2
DisjunctiveIntervalTemplate = DisjunctiveIntervalTemplate
PolyTemplate = PolyTemplate
DisjunctivePolyTemplate = DisjunctivePolyTemplate
OctagonTemplate = OctagonTemplate
ZoneTemplate = ZoneTemplate

BitVecIntervalTemplate = BitVecIntervalTemplate
DisjunctiveBitVecIntervalTemplate = DisjunctiveBitVecIntervalTemplate
BitVecZoneTemplate = BitVecZoneTemplate
DisjunctiveBitVecZoneTemplate = DisjunctiveBitVecZoneTemplate
BitVecOctagonTemplate = BitVecOctagonTemplate
DisjunctiveBitVecOctagonTemplate = DisjunctiveBitVecOctagonTemplate
BitVecAffineTemplate = BitVecAffineTemplate
DisjunctiveBitVecAffineTemplate = DisjunctiveBitVecAffineTemplate
BitVecPolyhedronTemplate = BitVecPolyhedronTemplate
DisjunctiveBitVecPolyhedronTemplate = DisjunctiveBitVecPolyhedronTemplate

