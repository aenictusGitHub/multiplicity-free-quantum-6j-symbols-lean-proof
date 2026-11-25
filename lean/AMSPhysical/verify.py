#!/usr/bin/env python3
"""Replay and audit the complete AMS Eq35 coefficient certificate in its stated domain."""
import argparse
import datetime
import hashlib
import json
import os
import platform
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path

MODULES = ['QuantumNumbers', 'QuantumLattice', 'QuantumLatticeRoots', 'QuantumIntegerRecurrence', 'QuantumLatticeSerre', 'QuantumTypeARoots', 'QuantumTypeASerre', 'QuantumTypeAAlgebra', 'QuantumOccupation', 'PreservingEndAlgebra', 'QuantumTypeAFinite', 'QuantumTypeAWeights', 'QuantumOccupationGraph', 'OccupationTensorCoefficients', 'QuantumOccupationPrefix', 'WeightedTranslation', 'QuantumPairRaising', 'QuantumMixedCreationCoefficients', 'QuantumCreationSingleShift', 'QuantumOccupationEnergy', 'FiniteWeightedHilbert', 'BilinearAdjoint', 'QuantumSL2', 'QuantumAlgebra', 'QuantumCoproduct', 'FiniteQuantumSL2', 'FiniteQuantumRepresentation', 'QuantumTensorRepresentation', 'QuantumPowers', 'QuantumClebsch', 'QuantumClebschClosed', 'FiniteQuantumClebsch', 'QuantumCasimir', 'QuantumIrreducible', 'Normalization', 'QuantumPositive', 'QuantumCasimirBaseSpectrum', 'QuantumStrings', 'QuantumNormalizedStrings', 'QuantumCasimirSpectrum', 'QuantumCoupledStrings', 'QuantumCoupledBasis', 'JointEigenCoordinates', 'QuantumStringTruncation', 'QuantumClebschMap', 'FiniteWeightActions', 'AnalyticSign', 'QuantumAnalyticCoefficients', 'QuantumMetric', 'QuantumOccupationFactorials', 'QuantumOccupationWeights', 'QuantumOppositeWeight', 'QuantumOccupationReflection', 'QuantumLatticeReflection', 'QuantumLatticeReflectSingle', 'WeightedTranslationAlgebra', 'QuantumTripleCreation', 'InjectedBasisSynthesis', 'InjectedBasisProperties', 'OccupationTripleCoefficients', 'QuantumOccupationActions', 'QuantumOccupationLowering', 'QuantumOccupationShifts', 'GaussianSeries', 'OccupationPowerSeries', 'QuantumPhysicalDimension', 'GaussianFactorial', 'QuantumOccupationCharacter', 'QuantumTypeAPivotalWeights', 'QuantumOccupationShiftActions', 'QuantumSerreSum', 'QuantumTypeARelations', 'QuantumTypeAInverseWeights', 'QuantumTypeAChevalley', 'JointSpectralSubmodule', 'QuantumTypeAIrreducible', 'QuantumTypeADualSymmetric', 'QuantumTensorSerre', 'QuantumTypeACoproductBasic', 'QuantumTypeACoproductSerre', 'QuantumTypeACoproductDistant', 'QuantumTypeACoproduct', 'QuantumTypeATensorRepresentation', 'QuantumMixedCoefficient', 'QuantumMixedTensor', 'TensorBasisDiagonal', 'QuantumMixedNonzero', 'QuantumOccupationAdjoint', 'QuantumTypeACompact', 'QuantumTypeADualForm', 'QuantumTypeAOppositeCompact', 'QuantumOppositeModuleCompact', 'TensorWeightedHilbert', 'WeightedBasisSum', 'QuantumMixedMetric', 'CompactTypeAPair', 'TensorTypeACompact', 'QuantumMixedCompact', 'QuantumReverseMixedTensor', 'QuantumTypeACounit', 'QuantumTypeAFunctional', 'QuantumTypeAIntertwiner', 'QuantumTypeATensorIntertwiner', 'QuantumIntertwiner', 'CompactQuantumPair', 'TensorQuantumCompact', 'QuantumTensorIntertwiner', 'QuantumAssociatorIntertwiner', 'QuantumTypeAAssociator', 'QuantumTypeAAssociatorInverse', 'QuantumReflectionCartan', 'QuantumTypeADynkinReflection', 'QuantumReflectionIntertwiner', 'QuantumDynkinChevalley', 'QuantumOppositeReflection', 'FiniteWeightedDuality', 'WeightedBasisEquivalence', 'QuantumReflectionMetric', 'QuantumDynkinCoproduct', 'QuantumDynkinTensor', 'TensorWeightedIsometries', 'QuantumMixedReflection', 'QuantumCreationRaisingScalar', 'QuantumCreationRaising', 'QuantumCreationLowering', 'QuantumCreationCartan', 'QuantumOccupationLoweredAction', 'QuantumMixedCoefficientAction', 'PairHighestBoundary', 'PairHighestExcess', 'QuantumMixedCoefficientRaising', 'QuantumMixedFiniteCreation', 'QuantumMixedCoefficientLowering', 'QuantumMixedWeight', 'QuantumMixedWeightPairs', 'TensorBasisSlices', 'QuantumMixedSum', 'QuantumMixedRaisingCoordinate', 'QuantumMixedCancellation', 'QuantumOccupationScalarUnique', 'QuantumMixedUnique', 'BasisSupportedInjection', 'QuantumMixedWeightSpace', 'QuantumMixedCoefficientCartan', 'QuantumMixedCreationIntertwiner', 'QuantumOccupationShiftNorm', 'QuantumOccupationUnitWeights', 'InvolutiveTwistedIntertwiner', 'QuantumReverseMixedCreation', 'QuantumReverseCreationBasis', 'OccupationTripleBasisProperties', 'QuantumFiniteTripleCreation', 'QuantumTypeAMixedTriple', 'QuantumPhysicalTripleMetric', 'QuantumTypeATripleCompact', 'QuantumTripleLeftTensorMetric', 'OccupationTensorSynthesis', 'FiniteIntegerPrefix', 'QuantumStrictPrefix', 'WeightedTranslationScalar', 'QuantumMixedAnnihilationCoefficients', 'QuantumOccupationAnnihilationSupport', 'QuantumMixedFiniteAnnihilation', 'QuantumMixedAnnihilationBalance', 'CompactJointAdjoint', 'FiniteWeightedAdjoint', 'QuantumMixedContraction', 'WeightedShiftMetricAdjoint', 'QuantumMixedRawAdjunction', 'QuantumCreationGeneralShift', 'QuantumTripleCreationShifts', 'QuantumTripleAnnihilation', 'QuantumTripleAnnihilationSupport', 'QuantumFiniteTripleAnnihilation', 'QuantumTripleMetricBalance', 'QuantumFiniteTripleAdjunction', 'TensorWeightedAdjunction', 'DefiniteBilinearDuality', 'BilinearMetricAdjoint', 'BilinearAdjointTransport', 'QuantumTripleLeftTensorAnnihilation', 'QuantumCreationBoundary', 'QuantumMixedCoefficientClosed', 'QuantumGaussianBlocks', 'QuantumMixedGenerating', 'OccupationPowerSeriesGeneral', 'QuantumMixedNormSlots', 'QuantumMixedNormSummand', 'QuantumMixedNormTerm', 'QuantumMixedNormSlotProduct', 'QuantumMixedNormSum', 'QuantumMixedNormClosed', 'QuantumPureOccupationNorms', 'QuantumOccupationEdges', 'QuantumOccupationEdgeSum', 'QuantumMixedHighest', 'QuantumMixedNormalization', 'MixedBoundaryOccupation', 'QuantumMixedFusionHighest', 'QuantumMixedFusionBoundary', 'QuantumMixedFusionIndex', 'QuantumMixedFusionWeight', 'QuantumMixedBoundarySupport', 'QuantumMixedHighestExpansion', 'KroneckerEigenExpansion', 'MixedFusionHighestUnique', 'QuantumMixedCreationHighest', 'QuantumMixedFusionNorm', 'QuantumMixedContractionHighest', 'QuantumCreationSpectralScalar', 'QuantumPairCoordinates', 'QuantumMixedHeight', 'GradedCommonHighest', 'BilinearCyclic', 'QuantumMixedHighestExistence', 'InvariantSupremum', 'PositiveHighestComplete', 'QuantumMixedFusionComplete', 'CyclicCommutantEigenvalue', 'QuantumMixedContractionSpectrum', 'EigenDisjointExpansion', 'QuantumMixedOutsideHighest', 'QuantumMixedContractionZero', 'QuantumCenteredProduct', 'QuantumTransferCoefficients', 'FiniteCommutatorSum', 'QuantumTransferCommutator', 'QuantumPrefixTelescoping', 'QuantumGeometricPowers', 'CrossLadderPowers', 'CoefficientSupport', 'QuantumTripleFirstSupport', 'QuantumTripleCupBase', 'QuantumTripleCrossPower', 'WeightedTranslationNaturality', 'QuantumTriplePairInsertion', 'QuantumRadialDiagonalSum', 'QuantumDimensionProductIdentity', 'QuantumOscillatorCrossCoefficients', 'QuantumMixedOscillator', 'QuantumTripleLeftOscillator', 'GradedWeightedTranslation', 'GradedCreationPowers', 'GradedOscillatorPowers', 'QuantumOscillatorLadderScalar', 'QuantumTripleLeftPowers', 'QuantumCupMonomial', 'CoefficientSupportPowers', 'QuantumTriplePositiveSupport', 'QuantumCupBoundaryPoint', 'QuantumTripleCreationBoundary', 'QuantumTripleBoundaryPowers', 'QuantumCupBoundaryDiagonal', 'TriangularCoordinates', 'TriangularFamilyIndependent', 'QuantumCupIndependent', 'QuantumCupLeftBidiagonal', 'QuantumTripleReverseInsertion', 'QuantumTripleRightOscillator', 'QuantumTripleRightPowers', 'QuantumCupReverseMonomial', 'QuantumRightTransferDefinitions', 'QuantumRightTransferCoefficients', 'FiniteQCommutatorSum', 'QuantumRightTransferCommutator', 'QuantumCommutingTransferPowers', 'QuantumTripleThirdSupport', 'QuantumTripleRightCrossPower', 'QuantumCupRightBidiagonal', 'QuantumCupBidiagonalEdges', 'QuantumCupRankShiftCoefficients', 'QuantumCupIndexSteps', 'QuantumCupTop', 'QuantumCupDiagonalDistinct', 'QuantumMixedRawChannelSpectrum', 'QuantumTypeALoweringWords', 'QuantumTypeAWordRaising', 'QuantumTypeAGeneratorInvariant', 'QuantumTypeALoweringSpan', 'CompactHighestOrthogonal', 'QuantumMixedFusionOrthogonal', 'BilinearCyclicIrreducible', 'QuantumMixedIrreducible', 'QuantumMixedFusionIrreducible', 'BilinearOrthogonalSum', 'InvariantRepresentationRestriction', 'InvariantFamilySum', 'RestrictedIrreducible', 'QuantumMixedFusionEquiv', 'CyclicTwistedEquivalence', 'QuantumReverseFusion', 'QuantumReverseRawSpectrum', 'QuantumTripleRightTensorAnnihilation', 'CompleteEigenchannel', 'QuantumMixedExactEigenspaces', 'ScaledAdjointRadial', 'QuantumFiniteTripleRadial', 'QuantumTripleRadialTensor', 'TensorEigenspace', 'LinearEigenspaceTransport', 'QuantumTripleExactChannels', 'QuantumTypeAInvariantTensor', 'QuantumTypeABending', 'DiagonalCoevaluation', 'DiagonalSnake', 'FiniteRightBending', 'QuantumTypeATripleIntertwiner', 'QuantumTypeAUnbending', 'AlgebraIntertwinerSpace', 'QuantumTypeAHomBending', 'QuantumDualSigns', 'QuantumTypeADualInvariant', 'QuantumReverseDualForm', 'QuantumReverseDualInvariant', 'QuantumTypeAVectorInvariant', 'CompactFunctionalAdjoint', 'QuantumReverseEvaluation', 'CompactTrivialHighest', 'QuantumTypeAPivotal', 'QuantumTypeADualEvaluation', 'QuantumSymmetricCoevaluation', 'QuantumSymmetricDualAdjoint', 'QuantumPhysicalSnake', 'QuantumMixedHomBending', 'AlgebraIntertwinerTargetEquiv', 'LinearCombinationGram', 'RangeGramEquivalence', 'PositiveFamilyEquiv', 'QuantumWordEvaluation', 'QuantumHighestGram', 'HighestCyclicTransport', 'PairedLoweringSpan', 'PairedLoweringInvariant', 'HighestCyclicIntertwining', 'CompactHighestRealization', 'CompactFormScaling', 'CompactHighestExtension', 'QuantumTripleCreationIntertwiner', 'QuantumTripleHighestBase', 'QuantumTripleHighestCoefficients', 'QuantumTripleCoordinateDegrees', 'QuantumCupPhysicalSupport', 'IndependentSpanTransport', 'QuantumCupSpan', 'QuantumPhysicalCupVectors', 'QuantumPhysicalCupHighest', 'QuantumTypeAHighestSpace', 'CompactHighestHomEquivalence', 'QuantumSymmetricHighestRealization', 'QuantumTripleHomEquiv', 'CyclicEigenHomCoordinates', 'QuantumMixedHomCoordinates', 'QuantumCupHomIndex', 'QuantumCupHighestWeight', 'QuantumCupHighestCoordinates', 'QuantumCupHighestComplete', 'QuantumCupRadialInvariant', 'QuantumCupRadialAction', 'QuantumCupRankReduction', 'QuantumPhysicalCupTransport', 'QuantumCupPhysicalMetric', 'QuantumCupPhysicalAdjoint', 'BilinearFormAdjoints', 'QuantumCupPulledMetric', 'BidiagonalPairGramUnique', 'QuantumCupGramUnique', 'QuantumCupRankMetricScale', 'QuantumCupUnitaryRankReduction', 'QuantumPhysicalCupUnitary', 'QuantumFullHighestRankReduction', 'QuantumCompleteHighestOperators', 'QuantumCompleteHighestLiteral', 'QuantumTotalTripleRadial', 'QuantumTripleZeroBoundaries', 'QuantumPhysicalTripleInstances', 'QuantumTripleGeneralChannels', 'TriangularSimpleSpectrum', 'QuantumCupSimpleSpectrum', 'QuantumCupRightSimpleSpectrum', 'QuantumCompleteHighestSimpleSpectrum', 'QuantumCupStandardEigenvalues', 'PhysicalTypeIChannelSpaces', 'TwoVertexOccupation', 'TwoVertexEmbedding', 'TwoVertexFullIntertwiner', 'TwoVertexReconstruction', 'TwoVertexMetric', 'TwoVertexIsometry', 'QuantumRankTwoAlgebra', 'RankTwoSymmetricEquivalence', 'RankTwoOppositeEquivalence', 'QuantumRankTwoCoproduct', 'QuantumRankTwoTensor', 'QuantumAdjoint', 'QuantumTensorMetric', 'RankTwoMixedTensorEquivalence', 'QuantumTripleMetric', 'QuantumTripleRepresentation', 'InvariantQuantumForm', 'QuantumIntertwinerMetric', 'QuantumClebschIntertwiner', 'QuantumClebschIsometry', 'QuantumRecouplingConstruction', 'RankTwoMixedTripleEquivalence', 'TypeAHighestSpaceEquivalence', 'RankTwoHighestEquivalence', 'QuantumClebschOrthogonality', 'BilinearOrthonormal', 'QuantumOrthonormalBasis', 'TensorWeightedOrthogonal', 'QuantumTreeOrthogonality', 'QuantumFusionBases', 'OrthonormalBasisChange', 'QuantumFusionRecoupling', 'QuantumTreeIntertwiner', 'QuantumIrrepCasimir', 'QuantumIntertwinerSpectrum', 'QuantumHighestOrthogonal', 'QuantumFusionHighest', 'QuantumRacahOrthogonality', 'QuantumHighestReconstruction', 'QuantumHighestSpan', 'GaussianBinomial', 'QuantumBinomialTheorem', 'QuantumTensorPowers', 'QuantumForgetIntertwiner', 'QuantumFactorials', 'SymmetricVandermonde', 'QuantumCouplingNormFormula', 'QuantumHighestNorm', 'QuantumCoupledExpansion', 'TensorCoefficientCollapse', 'QuantumClebschSingleSum', 'QuantumFirstProjection', 'QuantumProjectedRecoupling', 'QuantumClebschFirstZero', 'QuantumProjectedCoordinates', 'QuantumProjectedTriangular', 'QuantumFixedHighest', 'QuantumIntermediateCasimir', 'QuantumTensorCoordinates', 'QuantumCasimirCoordinates', 'QuantumRacahJacobi', 'QuantumJacobiStep', 'QuantumProjectedNext', 'QuantumChannelNeighbors', 'TriangularNeighbors', 'QuantumJacobiDiagonal', 'QuantumBoundaryRecoupling', 'QuantumCupFusionPaths', 'StandardCupHighestVectors', 'PhysicalTypeICouplingVectors', 'RankTwoIntertwinerRange', 'RankTwoMixedClebschChannels', 'QuantumReflectionInvolutive', 'RankTwoReverseClebschChannels', 'RankTwoCouplingTreeImages', 'TensorEigenImage', 'RankTwoTreeRadialEigenvectors', 'RankTwoTotalTreeEigenvectors', 'RankTwoHighestCouplingEigenvectors', 'PhysicalTypeICouplingEigenvectors', 'PhysicalTypeIChannelCouplings', 'PhysicalTypeIRankReduction', 'QuantumTypeAPivotEigen', 'QuantumOppositePivotal', 'QuantumMixedPivotal', 'QuantumMixedCanonicalCore', 'QuantumReverseFusionHighest', 'QuantumReverseNormalizedHighest', 'QuantumMixedHighestRealizations', 'CyclicSpanScale', 'QuantumMixedFusionRealization', 'CompactHighestTrace', 'TraceRestrictionCongruence', 'TraceRetractionDecomposition', 'TraceInvariantFusion', 'QuantumMixedIrrepDimension', 'MinimumDiagonalSumInversion', 'QuantumMixedDimensionDifference', 'QuantumMixedWeylScalar', 'QuantumMixedDimensionClosed', 'PhysicalTypeINormalization', 'QuantumClebschFactorial', 'QuantumClebschAnalytic', 'QuantumLeadingRegular', 'QShiftedFactorial', 'QRacahNewtonAlgebra', 'QRacahNewtonBasis', 'QRacahSeriesCoefficients', 'QRacahFiniteSeries', 'BasicHypergeometricTerm', 'BasicFourTerm', 'SaalschutzParameters', 'SaalschutzNormalizedParameters', 'SaalschutzTelescopingAlgebra', 'SaalschutzTermRecurrences', 'SaalschutzFiniteSum', 'SaalschutzAdmissible', 'NormalizedSaalschutz', 'QRacahLowerEndpoint', 'QRacahUpperEndpoints', 'IntegerPochhammer', 'SpinRacahParameters', 'SpinRacahEndpointPowers', 'SpinRacahEndpoints', 'QuantumRationalFactors', 'QRacahExponentForm', 'QRacahDeathFactor', 'QuantumRacahRates', 'SpinRacahChannels', 'QuantumNormRatios', 'QuantumNormNeighbors', 'QuantumJacobiNormSquares', 'QuantumPathNormNeighbors', 'QuantumJacobiEightFactors', 'QuantumNeighborRates', 'SpinRacahGauge', 'QuantumGaugeFactor', 'RacahTriangleWeights', 'RacahBoundarySquares', 'QRacahRegularizedAlgebra', 'QRacahRegularizedSeries', 'SpinRacahDifference', 'SpinRacahScale', 'JacobiDiagonalAlgebra', 'QNumberPowerBridge', 'QuantumDiagonalPhases', 'QuantumDiagonalRatesRegular', 'JacobiDiagonalZeroAlgebra', 'QuantumDiagonalRates', 'JacobiEigenvectorUniqueness', 'FiniteGridEigenvector', 'SpinRacahPhysicalEigenvector', 'QuantumClebschLast', 'QuantumEdgePowers', 'QuantumClebschLastFormula', 'QuantumClebschFirstFormula', 'QuantumBoundaryFormula', 'QuantumRacahUniqueness', 'SpinRacahPhysicalFormula', 'SpinSearsParameters', 'QShiftedProducts', 'SearsProductCancellation', 'SearsTermConvolution', 'TriangularSumReindex', 'SearsConvolution', 'SearsSecondSum', 'SearsCleared', 'SearsAdmissible', 'SpinSearsIdentity', 'PochhammerQuantumFactorial', 'SearsQuantumPhase', 'SearsFactorialTerm', 'SearsFactorialSupport', 'SpinSearsNatural', 'SpinRacahFactorialSum', 'PositivePochhammerFactorial', 'PochhammerRatioFactorial', 'SpinRacahEndpointFactorial', 'FirstOrderGridUnique', 'QuantumGaugeClosed', 'QuantumFirstChannel', 'QuantumRacahClosedFactorial', 'RacahRowNormalization', 'RacahSingleTerm', 'RacahBoundaryPhysical', 'AMSGeneral', 'PhysicalRacahKernel', 'PhysicalAMSLabels', 'PhysicalRacahNormalization', 'PhysicalWignerFormula', 'TypeIShiftedTriangleCoordinates', 'PositiveTwoChannelNormalization', 'PhysicalTypeIPrefactor', 'PhysicalTypeIAMSLabels', 'QuantumMixedZeroExternalChannels', 'QuantumTripleChannelsActual', 'PhysicalTypeIAMSFormula', 'AMSTriangleCoordinates', 'AMSAnalyticRegularity', 'ComplexQuantumFactorials', 'ComplexClebschCoefficients', 'ComplexClebschAnalytic', 'FiniteTensorCoefficient', 'TensorAssociatorCoordinate', 'QuantumTreeBasisCoordinates', 'ComplexTreeCoefficients', 'QuantumTripleBasisSum', 'ComplexRacahOverlap', 'ComplexRacahAnalytic', 'QuantumSymmetricTensor', 'QuantumSymmetricPivotal', 'QuantumSymmetricMetric', 'TwoVertexTensorEmbedding', 'TwoRowHighestBoundary', 'TwoRowFusionIndex', 'TwoRowHighestWeight', 'QuantumTwoRowNormalized', 'SymmetricHighestCoordinates', 'SymmetricHighestBoundary', 'SymmetricHighestExcess', 'QuantumSymmetricHighestBoundary', 'QuantumSymmetricBoundarySupport', 'QuantumSymmetricHighestExpansion', 'QuantumSymmetricGrade', 'QuantumSymmetricHighestExistence', 'QuantumSymmetricFusionComplete', 'QuantumSymmetricFusionOrthogonal', 'TwoRowHighestUnique', 'QuantumSymmetricFusionIrreducible', 'QuantumSymmetricFusionEquiv', 'QuantumTwoRowChannelEquality', 'QuantumTwoRowIrrepDimension', 'TwoRowFusionSumInversion', 'QuantumTwoRowDimensionDifference', 'QuantumTwoRowWeylScalar', 'QuantumTwoRowDimensionClosed', 'CompactInvariantRestriction', 'CompactHighestChannelMetric', 'CompactMetricAdjointIntertwiner', 'CompactHighestChannelTransfer', 'QuantumTwoRowCanonicalClebsch', 'QuantumTypeIILeftPair', 'QuantumTypeIICommonIndex', 'PhysicalTypeIINormalization', 'ComplexWeylDimensions', 'PhysicalTypeIOverlapNormalization', 'QuantumOppositeHomBending', 'QuantumReverseFusionRealization', 'OrthogonalFusionTransport', 'QuantumMixedCommutor', 'QuantumTypeIITriple', 'QuantumTypeIILeftTree', 'FiniteBendingRange', 'QuantumTypeIILeftChannel', 'TensorSubmoduleOrthogonal', 'QuantumTypeIILeftOrthogonal', 'QuantumTypeIILeftUnit', 'QuantumTypeIIDimension', 'QuantumTypeIILeftBasis', 'StandardFixedHighestBasis', 'TypeIIShiftedPaths', 'TypeIIShiftedPathEquivalence', 'TypeIIStandardShiftedBasis', 'BilinearBasisEquiv', 'TypeIIShiftedUnitEquivalence', 'StandardClebschAtLabel', 'StandardClebschAdjoint', 'StandardPairTransfer', 'StandardClebschFirstCoordinate', 'StandardPairFirstCoordinate', 'CompactHighestProjectionOrthogonal', 'CompactHighestBackTransfer', 'TwoVertexPairLowering', 'FiniteLoweringCyclic', 'TwoRowRootStrings', 'TwoRowRootStringsTotal', 'TwoRowTransportRootStrings', 'TwoRowBackTransferRootFormula', 'TwoRowTransferRootFormula', 'TwoVertexProjection', 'TwoVertexProjectionAdjoint', 'TwoVertexPairProjection', 'TwoRowBoundaryPairMap', 'TwoRowBoundaryPairLift', 'TwoRowBackBoundaryLift', 'TwoVertexPairProjectionAdjoint', 'AdjointBoundaryProjection', 'TwoRowBoundaryProjection', 'TwoVertexCupProjection', 'FiniteBendingNaturality', 'QuantumTypeIILeftBoundary', 'StandardBentPairHighest', 'StandardPairFirstInput', 'StandardBentCoefficientCancellation', 'FiniteSumSupportShift', 'StandardBentPairExpansion', 'StandardWeightReversal', 'StandardLeftBoundaryExpansion', 'StandardBentLeftTree', 'StandardBentPairLabel', 'TypeIIShiftedBentFamily', 'TypeIIShiftedBentLeftTree', 'QuantumCouplingBentNorm', 'TypeIIShiftedBendingScalar', 'StandardClebschDeterminantShift', 'TypeIIShiftedBoundaryTransport', 'QuantumCouplingDeterminantNorm', 'TypeIIDeterminantMetricScale', 'QuantumTypeIICompact', 'CompactHighestIntertwinerMetric', 'QuantumTypeIILeftTreeMetric', 'TwoVertexTripleProjection', 'QuantumTypeIIHighestBoundary', 'QuantumPositivePivot', 'FiniteBendingMetric', 'FiniteBendingWeightedSum', 'CompactHighestPartialIsometry', 'WeightedProjectionTrace', 'QuantumReverseLoop', 'QuantumTypeIILeftNormTrace', 'QuantumTwoRowPositiveDimension', 'QuantumTypeIILeftNormClosed', 'TypeIIShiftedUniversalNormalization', 'StandardClebschAtTotal', 'TwoRowBoundaryClebschAction', 'TwoRowBoundaryStandardTransfer', 'QuantumTypeIILeftRawBasis', 'TwoVertexRankTwoProjection', 'QuantumTypeIIHighestBoundaryInjective', 'QuantumTypeIIStandardBoundaryIdentification', 'TypeIIShiftedUnitCoordinates', 'TriangularSpanCoordinates', 'TypeIIShiftedCoordinateSpan', 'TypeIIShiftedCompleteCoordinates', 'TypeAHighestSpaceMap', 'QuantumTypeIIRightCreation', 'QuantumTypeIIBoundaryEquivalence', 'TwoVertexShiftSupport', 'TwoVertexCreationCompression', 'TwoVertexCreationFormula', 'QuantumTypeIICreationBoundary', 'StandardBoundaryCreationCoordinate', 'TypeIISelectedCoordinateExtension', 'RankTwoTypeIITripleEquivalence', 'RankTwoTypeIIHighestEquivalence', 'RankTwoTypeIIBoundary', 'StandardTypeIICreation', 'TypeIIStandardShiftedCreation', 'TypeIIBoundaryCreationRecurrence', 'QuantumDeterminantDifference', 'TypeIIDeterminantCreationScalar', 'TypeIICreationMetricRatio', 'TypeIIShiftedCreationTransport', 'TensorRightEigenchannel', 'TensorRightMapRange', 'PhysicalTypeICouplingBases', 'QuantumTypeIICompleteEquiv', 'OrthogonalFusionChannels', 'QuantumMixedCommutorChannels', 'TensorSubmoduleTransport', 'QuantumTypeIIRightChannels', 'RankTwoTypeIIRightChannel', 'TypeIIStandardShiftedRightBasis', 'QuantumMixedInputSpectrum', 'QuantumTypeIIRightBasis', 'QuantumTypeIICreationGram', 'TypeIIStandardShiftedCreationGram', 'OrthonormalChannelLine', 'GramEigenvectorGauge', 'TypeIIShiftedCreationGramForm', 'TypeIIShiftedRightUnitNorm', 'TypeIIRightSpectrumDistinct', 'TypeIIShiftedRightGauge', 'TypeIIShiftedTriangles', 'TypeIIShiftedPhysicalKernel', 'PhysicalTypeIIPrefactor', 'AMSTypeIITriangleCoordinates', 'QuantumTypeIIRecoupling', 'TypeIIReferenceWigner', 'TypeIICertificationGap', 'PhysicalTypeIIAMSFormula', 'PhysicalTypeIICalibratedGauge', 'PhysicalTypeIIOverlapNormalization', 'PhysicalTypeIIExactAMS', 'ComplexPhysicalWigner', 'ComplexPhysicalAnalytic', 'ComplexAMSExpression', 'ComplexPhysicalIdentityPrinciple', 'ComplexAMSCanonicalBranch', 'ComplexAMSMatrixBranch', 'ComplexCompatibleContinuation', 'PhysicalAMSComplexContinuation', 'ComplexMatrixContinuationSpace', 'PhysicalAMSGenericComplex', 'AMSClassicalLimit', 'AMSClassicalPhysicalValue', 'ComplexPhysicalClassicalLimit', 'AMS35Certificate', 'GlobalVertexSigns', 'AMSDynkinVertexPhase', 'AMSDynkinPhaseMixedRoles', 'GlobalSL2Vertices', 'AMSGlobalRankTwo', 'CyclicIntertwinerUnique', 'GlobalHighestCarrierCoherence', 'GlobalScalarHighestTransport', 'CompactHighestFullEmbedding', 'CompactHighestOnChannel', 'FullHighestEmbeddingCoherence', 'ActualHighestCarrier', 'GlobalVertexBending', 'GlobalTypeIILeftVertices', 'GlobalMixedCreationCoherence', 'GlobalMixedPairRealizations', 'GlobalMixedPairTransfers', 'PureMixedHighest', 'HighestFunctionalTransport', 'TensorHighestFunctional', 'OccupationHighestFunctional', 'OppositeLoweringCharge', 'MixedOrientationWordBoundary', 'GlobalMixedOrientationBoundary', 'OppositeHighestRealization', 'ActualAMSCarriers', 'HighestFunctionalCartan', 'OccupationCartanLine', 'ActualAMSBoundary', 'PositiveHighestVertexUnique', 'ActualPositiveVertexTable', 'ActualVertexTransport', 'ActualCarrierEquivalences', 'NativeInnerHighestLines', 'GlobalRightTreeBoundary', 'QuantumTypeIIChannelGauge', 'GlobalTypeIIRightBoundary', 'GlobalCupCreationCoherence', 'GlobalTypeIIRightStep', 'GlobalReverseMixedPairTransfers', 'NativeMixedCreationGeometry', 'GlobalCupFirstBoundary', 'GlobalCupBoundaryTransport', 'RankTwoTypeIFirstBoundary', 'PhysicalTypeIFirstBoundaryTransport', 'QuantumClebschSecondZero', 'StandardCupFirstBoundarySigns', 'PhysicalTypeIFirstBoundarySigns', 'PhysicalTypeIFirstBoundaryCreation', 'GlobalTensorChannelMetric', 'TensorChannelScaledMetric', 'TensorRightOnChannel', 'PhysicalTypeIRightCreationGeometry', 'TensorLeftOnChannel', 'PhysicalTypeILeftCreationGeometry', 'GlobalTypeILeftStep', 'GlobalTypeILeftFixedChannel', 'PhysicalTypeIHighestTreeEmbedding', 'GlobalTypeIIRightFixedChannel', 'PhysicalTypeIIHighestTreeEmbedding', 'GlobalTypeIIRightVertices', 'GlobalTypeILeftVertices', 'PhysicalAllFirstFunctional', 'MixedZeroHighestFunctional', 'StandardHighestFirstBoundary', 'GlobalCupHighestFirstBoundary', 'PhysicalHighestFirstBoundaryTransport', 'PhysicalLeftHighestFirstPositive', 'SymmetricEndpointCartan', 'ProjectedHighestCartan', 'MixedSymHighestBoundary', 'OccupationTensorHighestSlices', 'TensorWeightedBilinIntrinsic', 'ActualTwoRowVertexEntry', 'ActualForwardMixedVertexEntry', 'ReverseInnerBoundary', 'ReverseInnerHighestLine', 'GlobalMixedCommutorBoundary', 'GlobalTypeIRightStep', 'GlobalTypeIRightFixedChannel', 'GlobalTypeIRightIIComparison', 'GlobalSharedRightVertices', 'ActualReverseMixedVertexEntry', 'HighestLineEmbedding', 'PhysicalTripleIntrinsicMetrics', 'GlobalMixedSymInclusion', 'HighestSpaceMap', 'GlobalMixedSymHighestLine', 'ActualMixedSymVertexEntry', 'PureMixedCarrierBoundary', 'OppositeCartanLine', 'ActualMixedBoundaryCartan', 'SymMixedHighestBoundary', 'GlobalSymMixedInclusion', 'GlobalSymMixedHighestLine', 'ActualSymMixedVertexEntry', 'TwoRowOuterHighestFunctional', 'TwoRowOuterBoundaryPositive', 'TypeIIChannelHighestLine', 'NativeTypeIIVertices', 'NativeTypeIIOuterBoundary', 'ActualNativeTwoRowEntry', 'NativeTypeIIInclusion', 'NativeTypeIIOuterHighestLine', 'ActualTwoRowOuterEntry', 'ActualTwoRowDynkin', 'SharedActualAMSVertexTable', 'UnitIntertwinerFullIsometry', 'AMSOuterVerticesFullIsometry', 'ActualVertexTreeCoherence', 'AMSSharedNativeTreePhases', 'ActualUnitaryVertex', 'SharedActualAMSUnitary', 'ActualTreeFromEntries', 'ActualAMSTableTrees', 'ActualAMSQuadrilateralVectors', 'ActualAMSQuadrilateralComparison', 'ActualAMSRecoupling', 'ActualAMSCoefficientCertificate', 'ActualAMSVertexAliases', 'AMSSharedVertexCertificate', 'SplitOrbit', 'Determinant', 'Radial', 'Reduction', 'InvariantSL2', 'InvariantGL', 'InvariantFFT', 'PolynomialWeight', 'BalancedSL', 'Volterra', 'Bielecki', 'ChannelArithmetic', 'FixedDegrees', 'EulerDegrees', 'WeightedEuler', 'RelativeEquiv', 'SL2Charge', 'DeterminantDegrees', 'FixedEquivalences', 'Fock', 'FockOperators', 'FixedCasimir', 'FixedCasimirEnds', 'FixedSameCasimir', 'FockHilbert', 'FockEight', 'Polar', 'MatrixPolar', 'KZUniqueness', 'KZExistence', 'KZLocal', 'KZCanonical', 'KZAssociator', 'KZNaturality', 'KZCentralShift', 'HilbertMatrixReduction', 'FixedFockSpaces', 'KZIntertwining', 'ClassicalKZReduction', 'PolynomialAdjointGram', 'PairingLadderOperators', 'DeterminantFockNorm', 'DeterminantLadderTransport', 'PolynomialFockForm', 'UniversalFockNormalization', 'ClassicalUniversalNormalization', 'ClassicalUniversalIntertwining', 'ClassicalUniversalKZReduction', 'CompactHighestEqualWeight', 'QuantumMixedCanonicalTransport', 'QuantumMixedCanonicalClebsch', 'QuantumReverseCanonicalClebsch', 'GlobalMixedVertices', 'GlobalTypeILeftHighest', 'IrreducibleTwistedEquivalence', 'KZGauge', 'MatrixGauge', 'NormalizedBasisOperator', 'PhysicalHighestTreeEmbedding', 'PhysicalTypeIGaugeFormula', 'QuantumCoassociativity', 'QuantumExplicitRecurrence', 'QuantumMixedChannelRepresentation', 'QuantumMixedClebsch', 'QuantumPairHomogeneous', 'QuantumMixedOscillatorPowers', 'QuantumMixedRawIntertwiner', 'QuantumMixedSimple', 'QuantumOccupationDimension', 'QuantumReverseFusionIrreducible', 'QuantumTypeACoassociativity', 'QuantumTypeACounitLaws', 'QuantumTypeIICreationCoordinates', 'QuantumTypeIINormalizedCreation', 'QuantumTypeIICreationDimensionRatio', 'QuantumTypeIICreationRankFactor', 'QuantumTypeIILeftNormFactorial', 'QuantumTypeIILeftNormSum', 'QuantumTypeIIOverlapCoordinates', 'SL2FixedSpaces', 'SymmetricGaussianSeries', 'TypeIIAdjacentScalar', 'AMSPhysical', 'Audit']
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def individual_audit_source(names):
    return 'import AMSPhysical\n\n' + ''.join('#print axioms ' + n + '\n' for n in names)


def audit_source(names):
    """Traverse the complete union of all kernel-checked dependency graphs once."""
    return ('import AMSPhysical\nimport Lean.Util.CollectAxioms\n\nset_option maxRecDepth 65536\n\n'
            'open Lean Elab Command in\nrun_cmd do\n'
            '  let roots : Array Name := #[\n' +
            ',\n'.join('    `' + n for n in names) + '\n  ]\n'
            '  let env ← getEnv\n'
            '  for root in roots do\n'
            '    unless (env.checked.get.find? root).isSome do\n'
            '      throwError m!"Missing kernel declaration: {root}"\n'
            '  let action : CollectAxioms.M Unit := roots.forM CollectAxioms.collect\n'
            '  let (_, state) := (action.run env).run {}\n'
            '  logInfo m!"AUDITED_DECLARATIONS: {roots.size}"\n'
            '  logInfo m!"GLOBAL_AXIOMS: [{String.intercalate ", " (state.axioms.toList.map toString)}]"\n')


def parse_individual_audit(audit):
    audited = {name: [a.strip() for a in axioms.split(',') if a.strip()]
               for name, axioms in re.findall(
                   r"^'(.+)' depends on axioms: \[([^\]]*)\]$", audit, re.M)}
    for name in re.findall(r"^'(.+)' does not depend on any axioms$", audit, re.M):
        audited[name] = []
    return audited


def remove_comments_and_strings(source):
    """Preserve newlines; respect Lean's nested block comments."""
    out = []
    i = depth = 0
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                i += 2
            elif source.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif source.startswith('/-', i):
            depth = 1
            i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    out.append('\n' if source[i] == '\n' else ' ')
                    i += 1
        else:
            out.append(source[i])
            i += 1
    return ''.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', type=Path, default=Path(
        '/private/tmp/su2-lean-toolchain/lean-4.24.0-darwin_aarch64/bin/lean'))
    parser.add_argument('--mathlib', type=Path, default=Path(
        '/private/tmp/su2-lean-toolchain/mathlib'))
    parser.add_argument('--file', help='Debug replay of just one module; not a full audit')
    parser.add_argument('--jobs', type=int, default=1,
                        help='Parallel Lean processes for independent modules')
    parser.add_argument('--individual-audit', action='store_true',
                        help='Also compute exact per-declaration axiom lists (slower)')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    work = root / '.verification'
    build = work / 'build'
    build.mkdir(parents=True, exist_ok=True)
    mathlib = args.mathlib.resolve()
    paths = [build, mathlib / '.lake/build/lib/lean',
             *sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))]
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, paths)))
    lean = args.lean.resolve()
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    if '4.24.0' not in version:
        raise SystemExit('This certificate is pinned to Lean 4.24.0.')
    print(version, flush=True)

    names = [args.file] if args.file else [m + '.lean' for m in MODULES]
    expected = []
    theorem_names = []
    hashes = {}
    for module in MODULES:
        name = module + '.lean'
        source = (root / name).read_text()
        hashes[name] = hashlib.sha256(source.encode()).hexdigest()
        cleaned = remove_comments_and_strings(source)
        forbidden = re.search(r'\b(sorry|admit|axiom|unsafe)\b', cleaned)
        if forbidden:
            raise SystemExit(f'Forbidden declaration/placeholder in {name}: {forbidden[0]}')
        namespace = 'AMSGeneral' if module == 'AMSGeneral' else 'AMSPhysical'
        declarations = re.findall(
            r'(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s(:]+)', cleaned)
        expected.extend(namespace + '.' + n for kind, n in declarations)
        theorem_names.extend(namespace + '.' + n for kind, n in declarations if kind in ('theorem', 'lemma'))
    expected_audit = audit_source(expected)
    if (root / 'Audit.lean').read_text() != expected_audit:
        raise SystemExit('Audit.lean does not enumerate every declared theorem.')

    if args.jobs < 1:
        raise SystemExit('--jobs must be positive')
    combined = []
    dependencies = {name: {
        m + '.lean' for m in re.findall(r'(?m)^import (\w+)', (root / name).read_text())
        if m + '.lean' in names} for name in names}

    def check(name):
        # The combined audit elaborates thousands of roots in one command.
        stack_args = ['-s', '65536'] if name == 'Audit.lean' else []
        return subprocess.run(
            [str(lean), *stack_args, '-DwarningAsError=true', '-o',
             str(build / Path(name).with_suffix('.olean')), name],
            cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    pending = list(names)
    finished = set()
    running = {}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            ready = [name for name in pending if dependencies[name] <= finished]
            for name in ready[:max(0, args.jobs-len(running))]:
                print('CHECK', name, hashes[name], flush=True)
                running[pool.submit(check, name)] = name
                pending.remove(name)
            if not running:
                raise SystemExit('Dependency cycle in replay modules')
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in sorted(done, key=lambda f: running[f]):
                name = running.pop(future)
                result = future.result()
                print(result.stdout, end='', flush=True)
                (work / (Path(name).stem + '.log')).write_text(result.stdout)
                combined.append('CHECK ' + name + '\n' + result.stdout)
                (work / 'replay.log').write_text(version + '\n' + '\n'.join(combined))
                if result.returncode:
                    raise SystemExit(result.returncode)
                finished.add(name)
    for name, expected_hash in hashes.items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest() != expected_hash:
            raise SystemExit('Source changed during replay: ' + name)

    if args.file:
        print('PASS: selected module only; full audit not run.', flush=True)
        return
    audit = (work / 'Audit.log').read_text()
    counts = re.findall(r'AUDITED_DECLARATIONS: (\d+)', audit)
    unions = re.findall(r'GLOBAL_AXIOMS: \[([^\]]*)\]', audit)
    if counts != [str(len(expected))] or len(unions) != 1:
        raise SystemExit('Incomplete combined dependency audit.')
    axiom_union = sorted(a.strip() for a in unions[0].split(',') if a.strip())
    if set(axiom_union) - STANDARD_AXIOMS:
        raise SystemExit(f'Unapproved axiom dependencies: {axiom_union}')
    audited = None
    if args.individual_audit:
        audit_path = work / 'IndividualAudit.lean'
        audit_path.write_text(individual_audit_source(expected))
        result = subprocess.run(
            [str(lean), '-DwarningAsError=true', '-o', str(build / 'IndividualAudit.olean'),
             str(audit_path)], cwd=root, env=env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (work / 'IndividualAudit.log').write_text(result.stdout)
        if result.returncode:
            print(result.stdout, flush=True)
            raise SystemExit(result.returncode)
        audited = parse_individual_audit(result.stdout)
        if set(audited) != set(expected):
            raise SystemExit('Incomplete individual axiom audit.')
        individual_union = set().union(*(set(a) for a in audited.values()))
        if individual_union != set(axiom_union):
            raise SystemExit('Combined and individual dependency audits disagree.')
    certificate_theorems = ['AMSPhysical.AMS_Eq35_complete', 'AMSPhysical.physicalTypeI_AMS_Eq35_four_triangles', 'AMSPhysical.physicalTypeII_AMS_Eq35_calibrated', 'AMSPhysical.physicalTypeI_classical_AMS', 'AMSPhysical.physicalTypeII_classical_AMS', 'AMSPhysical.complexPhysicalTypeIWigner_at_one_actual_limit', 'AMSPhysical.complexPhysicalTypeIIWigner_at_one_actual_limit', 'AMSPhysical.physicalTypeI_AMS_Eq35_generic_complex', 'AMSPhysical.physicalTypeII_AMS_Eq35_generic_complex', 'AMSPhysical.physicalTypeI_AMS_all_complex_continuations', 'AMSPhysical.physicalTypeII_AMS_all_complex_continuations', 'AMSPhysical.typeIIShiftedUnitEquiv_creation', 'AMSPhysical.typeIIShiftedUnitEquiv_right']
    if not set(certificate_theorems).issubset(expected):
        raise SystemExit('Missing a required main AMS certificate theorem.')
    global_vertex_theorems = [
        'AMSPhysical.GlobalVertexSigns.pathSign_closed',
        'AMSPhysical.CompactHighestRealization.transport_comp',
        'AMSPhysical.CompactHighestRealization.channelTransfer_factor',
        'AMSPhysical.mixedCanonicalTransport_comp',
        'AMSPhysical.mixedCanonicalTransport_reverse_coherent',
        'AMSPhysical.physicalTypeI_global_vertices_rank_two',
        'AMSPhysical.physicalTypeII_global_vertices_rank_two',
        'AMSPhysical.physicalTypeIILeftTreeMap_global_factor',
        'AMSPhysical.physicalTypeIICalibratedLeft_global_scale',
        'AMSPhysical.quantumCupRankReduction_create_left',
        'AMSPhysical.quantumCupRankReduction_create_right',
        'AMSPhysical.quantumCupMonomial_first_boundary',
        'AMSPhysical.quantumCupRankReduction_first_boundary',
        'AMSPhysical.mixedFiniteCreation_channel_transport',
        'AMSPhysical.physicalTypeIICalibratedRight_first_boundary_pos',
        'AMSPhysical.physicalTypeIICalibratedRight_unique_positive',
        'AMSPhysical.physicalTypeIICalibratedRight_creation',
        'AMSPhysical.exists_shared_actual_unitary_AMS_vertex_table',
        'AMSPhysical.amsActualVertexTable_shared',
        'AMSPhysical.amsActualVertexTable_unitary',
        'AMSPhysical.nativeTypeIITwoRow_rank_three_mixed_alias',
        'AMSPhysical.actualTypeIRecouplingMatrix_calibrated',
        'AMSPhysical.actualTypeIIRecouplingMatrix_calibrated',
        'AMSPhysical.actualTypeI_AMS_Eq35_shared_vertices',
        'AMSPhysical.actualTypeII_AMS_Eq35_shared_vertices',
        'AMSPhysical.amsDynkinVertexPhase_closed_path',
        'AMSPhysical.AMS_Eq35_shared_actual_vertex_certificate',
    ]
    if not set(global_vertex_theorems).issubset(expected):
        raise SystemExit('Missing a required shared actual vertex certificate theorem.')
    report = {
        'component_certificate_passed': True,
        'full_AMS_certified': True,
        'positive_real_both_types_certified': True,
        'physical_classical_limit_certified': True,
        'compatible_complex_continuations_certified': True,
        'certificate_theorems': certificate_theorems,
        'global_vertex_phase_coherence_certified': True,
        'shared_actual_vertex_table_both_families_N_ge_3_certified': True,
        'global_vertex_scope': 'One actual Dynkin-indexed table, all six AMS roles, full-algebra intertwining and isometry, and exact recoupling coefficients for BOTH families; N>=3, real q>0, q!=1. Rank two is covered separately. This actual-table theorem does not assert a separately implemented classical or arbitrary-complex tensor category or a full pentagon matrix identity.',
        'rank_two_global_vertex_coherence_certified': True,
        'global_vertex_progress_theorems': global_vertex_theorems,
        'global_vertex_remaining': [],
        'scope': 'AMS Eq35 coefficient identity for both physical types, every rank and admissible label: exact actual positive-real q != 1 formula in explicitly specified unit channel gauges; actual physical q=1 deformation limits and their independent finite CG identification; equality of the full maximal compatible complex analytic continuation families of the whole coefficient matrix. One shared actual Dynkin-indexed isometric intertwiner table additionally realizes both families at N>=3, real q>0,q!=1, with exact AMS coefficients and all aliases identified. Physical base coefficients and their CG continuation are constructed independently of the AMS candidate. Complex scope is analytic continuation, not a separately implemented arbitrary-complex higher-rank tensor category.',
        'checked_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'host': platform.node(), 'platform': platform.platform(), 'lean': version,
        'lean_executable': str(lean), 'mathlib_directory': str(mathlib),
        'mathlib_release': 'v4.24.0',
        'parallel_jobs': args.jobs,
        'audit_thread_stack_kb': 65536,
        'module_count': len(MODULES), 'theorem_count': len(theorem_names),
        'declaration_count': len(expected),
        'source_sha256': hashes,
        'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'axiom_audit_mode': 'complete transitive union over every declaration root',
        'audited_declarations': expected,
        'axiom_union': axiom_union,
        'theorem_axioms': audited,
        'remaining': [],
    }
    (work / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'PASS: {len(theorem_names)} theorems and {len(expected)-len(theorem_names)} definitions kernel-checked; only standard Lean axioms.', flush=True)
    print('FULL AMS COEFFICIENT THEOREM: CERTIFIED in the parameter and channel conventions documented in README.txt.', flush=True)


if __name__ == '__main__':
    main()
