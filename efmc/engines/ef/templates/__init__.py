# coding: utf-8
from .abstract_template import TemplateType, Template
from .interval import IntervalTemplate, DisjunctiveIntervalTemplate, IntervalTemplateV2
from .zone import ZoneTemplate
from .octagon import OctagonTemplate
from .affine import AffineTemplate, DisjunctiveAffineTemplate
from .polyhedron import PolyTemplate, DisjunctivePolyTemplate

from .bv_interval import BitVecIntervalTemplate, DisjunctiveBitVecIntervalTemplate
from .bv_zone import BitVecZoneTemplate, DisjunctiveBitVecZoneTemplate
from .bv_octagon import BitVecOctagonTemplate, DisjunctiveBitVecOctagonTemplate
from .bv_affine import BitVecAffineTemplate, DisjunctiveBitVecAffineTemplate
from .bv_polyhedron import BitVecPolyhedronTemplate, DisjunctiveBitVecPolyhedronTemplate

# Export (TODO: maybe export shorter names)
TemplateType = TemplateType
IntervalTemplate = IntervalTemplate
IntervalTemplateV2 = IntervalTemplateV2
DisjunctiveIntervalTemplate = DisjunctiveIntervalTemplate
ZoneTemplate = ZoneTemplate
OctagonTemplate = OctagonTemplate
AffineTemplate = AffineTemplate
DisjunctiveAffineTemplate = DisjunctiveAffineTemplate
PolyTemplate = PolyTemplate
DisjunctivePolyTemplate = DisjunctivePolyTemplate


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
