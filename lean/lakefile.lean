import Lake
open Lake DSL

package kakeya_verification

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target] lean_lib Scalar
@[default_target] lean_lib Finite
@[default_target] lean_lib Reduction
@[default_target] lean_lib Laminar
@[default_target] lean_lib Configurations
@[default_target] lean_lib Endpoint
@[default_target] lean_lib LogLoss
@[default_target] lean_lib ErrorAbsorption
@[default_target] lean_lib CapSelection
@[default_target] lean_lib TubeGeometry
@[default_target] lean_lib Sampling
@[default_target] lean_lib GridGeometry
@[default_target] lean_lib Localization
@[default_target] lean_lib MeasurableOccupancy
@[default_target] lean_lib MeasurableLocalization
@[default_target] lean_lib PivotSupport
@[default_target] lean_lib SamplingApplication
@[default_target] lean_lib TubeLocalCount
@[default_target] lean_lib GridCells
@[default_target] lean_lib DensityNormalization
@[default_target] lean_lib TubeVolume
@[default_target] lean_lib ProjectiveGeometry
@[default_target] lean_lib PivotWitnesses
@[default_target] lean_lib OccupancySelection
@[default_target] lean_lib ScaleChoice
@[default_target] lean_lib UniformLocalization
@[default_target] lean_lib Rescaling
@[default_target] lean_lib CapCover
@[default_target] lean_lib PivotDirections
@[default_target] lean_lib TubeIntersection
@[default_target] lean_lib DiscreteMeasurable
@[default_target] lean_lib Bush
@[default_target] lean_lib CapThinningGeometry
@[default_target] lean_lib EuclideanSplit
@[default_target] lean_lib HairbrushPlanes
@[default_target] lean_lib MeasurableEnergy
@[default_target] lean_lib FamilyLocalization
@[default_target] lean_lib MeasurableEstimate
@[default_target] lean_lib AngularDecomposition
@[default_target] lean_lib AngularIncidence
@[default_target] lean_lib AngularAssignment
@[default_target] lean_lib ThickCircle
@[default_target] lean_lib PlanarEnergy
@[default_target] lean_lib CommonDensityLocalization
@[default_target] lean_lib MeasurableRescaling
@[default_target] lean_lib LiftGraph
@[default_target] lean_lib LiftSegments
@[default_target] lean_lib GroupedIncidence

@[default_target] lean_lib Coarsening
@[default_target] lean_lib BallPruning
@[default_target] lean_lib CumulativeEstimate
@[default_target] lean_lib CoarseFamily
@[default_target] lean_lib GroupedCumulative
@[default_target] lean_lib HeavyIncidence
@[default_target] lean_lib PrunedIncidence
@[default_target] lean_lib SpatialAngular
@[default_target] lean_lib SpatialSplitting
@[default_target] lean_lib SpatialAssignment
@[default_target] lean_lib HairbrushUnion
@[default_target] lean_lib HairbrushRemoval
@[default_target] lean_lib HairbrushStem
@[default_target] lean_lib HairbrushSelection
@[default_target] lean_lib HairbrushBroad
@[default_target] lean_lib HairbrushFractional
@[default_target] lean_lib HairbrushScales
@[default_target] lean_lib HairbrushCoarse
@[default_target] lean_lib GridShadingMeasure
@[default_target] lean_lib WidthNormalization

@[default_target] lean_lib HairbrushAllScales
@[default_target] lean_lib AnisotropicRescaling

@[default_target] lean_lib HairbrushKernel
@[default_target] lean_lib HairbrushLogLoss
@[default_target] lean_lib GridMarked
@[default_target] lean_lib GridHairbrush
@[default_target] lean_lib LocalizedClusters
@[default_target] lean_lib DensityBroadnessRecovery
@[default_target] lean_lib RecoveredHairbrush
@[default_target] lean_lib AnisotropicVolume
@[default_target] lean_lib AnisotropicDirections
@[default_target] lean_lib AnisotropicCap

@[default_target] lean_lib AnisotropicGrid
@[default_target] lean_lib AnisotropicShading
@[default_target] lean_lib AnisotropicTransport
@[default_target] lean_lib GridTwoEnds
@[default_target] lean_lib LocalizedGridTubes
@[default_target] lean_lib MeasurableDensityRecovery
@[default_target] lean_lib MeasurableToDiscrete
@[default_target] lean_lib PrunedGraphLift
@[default_target] lean_lib SeparationColoring

@[default_target] lean_lib AnisotropicConfiguration
@[default_target] lean_lib LiftedAnalytic
@[default_target] lean_lib CoarseBounds
@[default_target] lean_lib AngleFiberSelection
@[default_target] lean_lib AngularBoxSelection
@[default_target] lean_lib AngularBoxRecovery
@[default_target] lean_lib AngularBoxHairbrush
@[default_target] lean_lib AngularBoxAlgebra
@[default_target] lean_lib AngularBoxLogLoss
@[default_target] lean_lib LegalParameterSelection
@[default_target] lean_lib LegalTubeSamples

@[default_target] lean_lib LegalSampleNormalization
@[default_target] lean_lib TransverseAngles
@[default_target] lean_lib LegalAngleSamples
@[default_target] lean_lib LegalAngleNormalization
@[default_target] lean_lib PivotOutputCount
@[default_target] lean_lib RawSampleTransfer
@[default_target] lean_lib LegalLabeledSamples
@[default_target] lean_lib LegalSampleOutputs
@[default_target] lean_lib LegalSampleSelection
@[default_target] lean_lib PivotKappa
@[default_target] lean_lib PivotKappaScale
@[default_target] lean_lib MarkedLegalSamples
@[default_target] lean_lib AngularGroupRestriction
@[default_target] lean_lib AngularGroupPruning
@[default_target] lean_lib AngularSeedPieces
@[default_target] lean_lib AngularSeedRealization
@[default_target] lean_lib AngularSeedSummation
@[default_target] lean_lib AngularSeedHairbrush
@[default_target] lean_lib AngularSeedBound
@[default_target] lean_lib AngularSeedLogLoss
@[default_target] lean_lib AngularSeedEstimate

@[default_target] lean_lib SelectedFiberLift

@[default_target] lean_lib SelectedFiberSlab

@[default_target] lean_lib SlabNormalization

@[default_target] lean_lib SelectedSlabGeometry

@[default_target] lean_lib LegalOutputDirections

@[default_target] lean_lib CollisionPlane

@[default_target] lean_lib CollisionIntersection

@[default_target] lean_lib ActualPivotFiberCount

@[default_target] lean_lib CollisionRows

@[default_target] lean_lib CollisionEnergy

@[default_target] lean_lib ActualLabelSelection

@[default_target] lean_lib ActualCollisionSelection

@[default_target] lean_lib LocalizedDirectionThinning

@[default_target] lean_lib LocalizedSeedNormalization

@[default_target] lean_lib FiniteGridLocalization

@[default_target] lean_lib FiniteLocalizedFamily

@[default_target] lean_lib SeedCoverNormalization

@[default_target] lean_lib LocalizedSeedApplication

@[default_target] lean_lib SeedGlobalizationAlgebra

@[default_target] lean_lib CoveredSeed

@[default_target] lean_lib FractionalSeed

@[default_target] lean_lib SeededEndpoint

@[default_target] lean_lib SelectedLiftWitness

@[default_target] lean_lib MarkedPruningRecovery

@[default_target] lean_lib MarkedPruningAssembly

@[default_target] lean_lib ActualGroupedIncidence

@[default_target] lean_lib ActualGroupedGeometry

@[default_target] lean_lib GroupedSlabPositions

@[default_target] lean_lib PivotSelectionBudgets

@[default_target] lean_lib PivotOutputLowerBound

@[default_target] lean_lib ClosingEnergyAlgebra

@[default_target] lean_lib MarkedSubsetSamples

@[default_target] lean_lib MarkedSpatialPruning

@[default_target] lean_lib PrunedScaleTransport

@[default_target] lean_lib MarkedPivotSelection

@[default_target] lean_lib PivotGeometryScale

@[default_target] lean_lib SelectedOutputPairs

@[default_target] lean_lib SelectedOutputSlabs

@[default_target] lean_lib SelectedOutputWitness

@[default_target] lean_lib SelectedOutputDensity

@[default_target] lean_lib SelectedOutputClosing

@[default_target] lean_lib RecoveredNormalizedBall

@[default_target] lean_lib PrunedPivotSelection

@[default_target] lean_lib UniformPrunedPivotSelection

@[default_target] lean_lib PivotFourthPower

@[default_target] lean_lib SelectedBaseFamilies

@[default_target] lean_lib SelectedColoredFamilies

@[default_target] lean_lib SelectedFamilyPruning

@[default_target] lean_lib OriginalPivotSlabs

@[default_target] lean_lib ConstructedPivotClosing

@[default_target] lean_lib OriginalPivotEnergy

@[default_target] lean_lib PivotLossAbsorption

@[default_target] lean_lib OriginalPivotScalar

@[default_target] lean_lib OriginalMarkedPivot

@[default_target] lean_lib MinPivotKappa

@[default_target] lean_lib MarkedPivotEstimate

@[default_target] lean_lib GenericMarkedPivotSelection

@[default_target] lean_lib SamplingCapTests

@[default_target] lean_lib SamplingBallTests

@[default_target] lean_lib SamplingSupport

@[default_target] lean_lib SamplingThreshold

@[default_target] lean_lib SamplingMeans

@[default_target] lean_lib SamplingDichotomy

@[default_target] lean_lib SamplingTheta

@[default_target] lean_lib SamplingRealization

@[default_target] lean_lib SamplingRowNormalization

@[default_target] lean_lib SamplingExactDensity

@[default_target] lean_lib SamplingNormalizedMeans

@[default_target] lean_lib SamplingMeasurableAssembly

@[default_target] lean_lib SamplingPivotInterface

@[default_target] lean_lib SampledMarkedEstimate

@[default_target] lean_lib TransformedGridSupport

@[default_target] lean_lib AngularPiecePopulation

@[default_target] lean_lib TransformedSamplingPopulation

@[default_target] lean_lib ExternalAxioms

@[default_target] lean_lib MarkedDensityClass

@[default_target] lean_lib AngularRestrictedRefinement

@[default_target] lean_lib AngularRestrictedMeasurable

@[default_target] lean_lib AnisotropicJointShading

@[default_target] lean_lib MeasurableMarkedSelection

@[default_target] lean_lib AnisotropicJointRecovery

@[default_target] lean_lib AnisotropicJointGeometry

@[default_target] lean_lib AnisotropicSamplingInput

@[default_target] lean_lib SpatialMarkedPartition

@[default_target] lean_lib ActualSpatialMarked

@[default_target] lean_lib SpatialMarkedGroups

@[default_target] lean_lib SixDimensionalCore

@[default_target] lean_lib LowCellAbsorption

@[default_target] lean_lib SamplingMeasurablePivot

@[default_target] lean_lib SamplingHighDensity

@[default_target] lean_lib SamplingOriginalCells

@[default_target] lean_lib SpatialGridPopulation

@[default_target] lean_lib AnisotropicSamplingRetention

@[default_target] lean_lib AnisotropicSamplingBudgets

@[default_target] lean_lib TwoEndsGlobalizationAlgebra

@[default_target] lean_lib AnisotropicDensityPower

@[default_target] lean_lib AnisotropicHighDensity

@[default_target] lean_lib AngularRefinementBudgets

@[default_target] lean_lib AngularSpatialBudgets

@[default_target] lean_lib LocalAngularCoarse

@[default_target] lean_lib AngularSpatialSampling

@[default_target] lean_lib LocalAngularLowDensity

@[default_target] lean_lib LocalAngularLowDensityOriginal

@[default_target] lean_lib AngularBoxHighDensity

@[default_target] lean_lib AngularBoxLowDensity

@[default_target] lean_lib AngularBoxCoarse

@[default_target] lean_lib AngularBoxAllCases

@[default_target] lean_lib AngularSpatialSummation

@[default_target] lean_lib AllAnglePivot

@[default_target] lean_lib SixDimensionalAllAngles

@[default_target] lean_lib AllAngleSeparation

@[default_target] lean_lib TwoEndsDiscreteEstimate

@[default_target] lean_lib TwoEndsPivot

@[default_target] lean_lib LocalizedCellPartition

@[default_target] lean_lib LocalizedGroupedNormalization

@[default_target] lean_lib LocalizedTwoEndsApplication

@[default_target] lean_lib TwoEndsGlobalization

@[default_target] lean_lib UnrestrictedPivot

@[default_target] lean_lib MaximalShading

@[default_target] lean_lib SixDimensionalUnrestricted

@[default_target] lean_lib DiagonalWeakening

@[default_target] lean_lib MainEndpoint

@[default_target] lean_lib MeasurableUnitPartition

@[default_target] lean_lib MaximalPositionReduction

@[default_target] lean_lib MainMaximal


@[default_target] lean_lib KakeyaOperator
@[default_target] lean_lib IndicatorWitnessCover
@[default_target] lean_lib KakeyaOperatorLaws
@[default_target] lean_lib SphereCapMeasure
@[default_target] lean_lib TubeIsometryVolume
@[default_target] lean_lib KakeyaOperatorL1
@[default_target] lean_lib TubeOpenCarrier
@[default_target] lean_lib ParameterLIntegral
@[default_target] lean_lib KakeyaOperatorMeasurability
@[default_target] lean_lib IndicatorRestrictedWeak
@[default_target] lean_lib OperatorRestrictedWeak
@[default_target] lean_lib RestrictedInterpolation
@[default_target] lean_lib RestrictedOperatorLaws
@[default_target] lean_lib OperatorScaleAlgebra
@[default_target] lean_lib RestrictedDyadic

@[default_target] lean_lib ENNRealLayerCake
@[default_target] lean_lib PowerKernel
@[default_target] lean_lib DyadicStrong
@[default_target] lean_lib DyadicApproximation
@[default_target] lean_lib DyadicOperatorExtension
@[default_target] lean_lib RestrictedStrong
@[default_target] lean_lib StrongTruncation
@[default_target] lean_lib TruncationKernels
@[default_target] lean_lib TruncationIntegral
@[default_target] lean_lib StrongInterpolation
@[default_target] lean_lib StrongInterpolationAlgebra
@[default_target] lean_lib OperatorNormConversion
@[default_target] lean_lib OperatorStrongEstimate
@[default_target] lean_lib OperatorNorm
@[default_target] lean_lib MainOperator
@[default_target] lean_lib FractionalSeedFullRange
@[default_target] lean_lib RadialPencil
@[default_target] lean_lib RadialSharpness

@[default_target] lean_lib WeightedAngularAssignment
@[default_target] lean_lib WeightedAngularSelection
@[default_target] lean_lib AngularSeedSqrtCap
@[default_target] lean_lib MeasurableIncidenceAtoms
@[default_target] lean_lib MeasurableAngularGroups
@[default_target] lean_lib MeasurableAngularPruning
@[default_target] lean_lib MeasurableAngularPieces
@[default_target] lean_lib MeasurableAngularHairbrush
@[default_target] lean_lib MeasurableSeedLogLoss
@[default_target] lean_lib MeasurableSeedEstimate
@[default_target] lean_lib DensityLogNormalization
@[default_target] lean_lib MeasurableDensityTrimming
@[default_target] lean_lib AdmissiblePivotSlabs
@[default_target] lean_lib AdmissiblePivotClosing
@[default_target] lean_lib SourceMarkedPivot
@[default_target] lean_lib LowerDensityEstimate
@[default_target] lean_lib PositiveDensityPruning
@[default_target] lean_lib PositivePivotSlabs
@[default_target] lean_lib PositivePivotAlgebra
@[default_target] lean_lib SourceMarkedPivotFullRange
@[default_target] lean_lib SamplingParameterRange
@[default_target] lean_lib SamplingRawMeans
@[default_target] lean_lib SamplingRawAssembly
@[default_target] lean_lib SamplingRawRealization
@[default_target] lean_lib SamplingClosedCaps
@[default_target] lean_lib SamplingGeometry
@[default_target] lean_lib SamplingBoundedSupport
@[default_target] lean_lib SamplingLengthInput
@[default_target] lean_lib SamplingLengthAssembly
@[default_target] lean_lib SamplingLengthRealization
@[default_target] lean_lib ProjectionConclusion
@[default_target] lean_lib AppendixEndpoints
@[default_target] lean_lib AbsoluteCapEstimates
@[default_target] lean_lib AbsoluteCapGlobalization
@[default_target] lean_lib LiftedCumulativeInput
@[default_target] lean_lib SourceMarkedPivotInputs
@[default_target] lean_lib DiscreteScaleCompletion
@[default_target] lean_lib SourceAnalyticInputs
@[default_target] lean_lib SourceMarkedPivotSmallScaleInputs
@[default_target] lean_lib PositiveMarkedPivotEstimate
@[default_target] lean_lib PositiveSampledMarkedEstimate
@[default_target] lean_lib PositiveSamplingMeasurablePivot
@[default_target] lean_lib PositiveSamplingHighDensity
@[default_target] lean_lib PositiveSamplingOriginalCells
@[default_target] lean_lib PositiveAnisotropicHighDensity
@[default_target] lean_lib PositiveAngularBoxHighDensity
@[default_target] lean_lib PositiveAngularBoxAllCases
@[default_target] lean_lib PositiveAllAnglePivot
@[default_target] lean_lib PositiveAllAngleSeparation
@[default_target] lean_lib PositiveTwoEndsPivot
@[default_target] lean_lib PositiveTwoEndsSmallScaleInputs
@[default_target] lean_lib WideTwoEndsEstimate
@[default_target] lean_lib PositiveWideTwoEndsPivot
@[default_target] lean_lib SpatialTubeCover
@[default_target] lean_lib MeasurableAngularSpatial
@[default_target] lean_lib MeasurableAngularDecomposition
@[default_target] lean_lib OriginalLowerDensity
@[default_target] lean_lib MeasurableSeedGeometry
@[default_target] lean_lib MeasurableSeedLengths
@[default_target] lean_lib MeasurableSeedDensity
@[default_target] lean_lib MeasurableSeedDensityLengths

-- Checkpoint 21: source conventions and original projection ingredients.
@[default_target] lean_lib SpatialTubeLengths
@[default_target] lean_lib MarkedGridRefinement
@[default_target] lean_lib ComplexOperator
@[default_target] lean_lib SourceGoodMass
@[default_target] lean_lib LengthTubeVolume
@[default_target] lean_lib ProjectiveAngleComparison
@[default_target] lean_lib GaussianMatrix
@[default_target] lean_lib CollisionIndependentSet
@[default_target] lean_lib GaussianCollisionKernel
@[default_target] lean_lib ProjectedGrid
@[default_target] lean_lib MeasurableAngularSpatialLengths
@[default_target] lean_lib MarkedGridPadding
@[default_target] lean_lib SourceDensityPruning
@[default_target] lean_lib MaximalLengths
@[default_target] lean_lib GaussianSmallBall
@[default_target] lean_lib GaussianLinearOperator
@[default_target] lean_lib ProjectedGridFamily
@[default_target] lean_lib MarkedGridNormalization
@[default_target] lean_lib SourceDensityPruningGeometry
@[default_target] lean_lib MeasurableLengthEstimates
@[default_target] lean_lib GaussianPerpendicular
@[default_target] lean_lib GaussianMatrixMoments
@[default_target] lean_lib MarkedNormalizationKappa
@[default_target] lean_lib MarkedLengthNormalization
@[default_target] lean_lib GaussianConditioning
@[default_target] lean_lib GaussianGoodDirections
@[default_target] lean_lib DilationIntegral
@[default_target] lean_lib MarkedNormalizationAlgebra
@[default_target] lean_lib MarkedLengthInput
@[default_target] lean_lib MinPivotLogBudget
@[default_target] lean_lib UnmarkedLengthEstimates
@[default_target] lean_lib GaussianCollisionGeometry
@[default_target] lean_lib LengthOperatorGeometry
@[default_target] lean_lib SourceMarkedNormalization
@[default_target] lean_lib MarkedLengthAlgebra
@[default_target] lean_lib SourceUnmarkedLengths
@[default_target] lean_lib GaussianCollision
@[default_target] lean_lib LengthOperatorBound
@[default_target] lean_lib SourceMarkedLengths
@[default_target] lean_lib GaussianCollisionExpectation
@[default_target] lean_lib LengthOperatorNorm

-- Checkpoint22: original Gaussian, sampling-net, and bush proof routes.
@[default_target] lean_lib GaussianRealization
@[default_target] lean_lib GaussianCollisionSelection
@[default_target] lean_lib GaussianSelectionAlgebra
@[default_target] lean_lib FiveDimensionalLengthSeed
@[default_target] lean_lib ProjectiveSphereNet
@[default_target] lean_lib CumulativeLengths
@[default_target] lean_lib BushLengths
@[default_target] lean_lib BushIteration
@[default_target] lean_lib SamplingGeometricFailure
@[default_target] lean_lib GaussianProjectedSelection
@[default_target] lean_lib SphereNetCapTests
@[default_target] lean_lib SphereNetBudget
@[default_target] lean_lib BushIterationConsequences
@[default_target] lean_lib GaussianProjectedFamily
@[default_target] lean_lib GaussianProjectionAlgebra
@[default_target] lean_lib SphereNetExactBudget
@[default_target] lean_lib SphereNetFailure
@[default_target] lean_lib SphereNetSampleRealization
@[default_target] lean_lib GaussianProjectionSeed
@[default_target] lean_lib SphereNetSourceFailure
@[default_target] lean_lib SamplingJointProbability
@[default_target] lean_lib GaussianNormalizedSeed
@[default_target] lean_lib SamplingSourceGeometricFailure
@[default_target] lean_lib SamplingSourceProbability
@[default_target] lean_lib SamplingSourceRealization

-- Checkpoint23: exact fixed-error and completed-measure source scope.
@[default_target] lean_lib CumulativeFixedError
@[default_target] lean_lib LebesgueRepresentatives
@[default_target] lean_lib LebesgueMaximal
@[default_target] lean_lib LebesgueRealCap
@[default_target] lean_lib LebesgueDensityPruning
@[default_target] lean_lib LebesgueLocalization
@[default_target] lean_lib LebesgueAngularSpatial
@[default_target] lean_lib LebesgueSeedDensity
@[default_target] lean_lib LebesgueSampling
@[default_target] lean_lib LebesgueHairbrush
@[default_target] lean_lib LebesgueSamplingSource
@[default_target] lean_lib LebesgueSamplingGeometry

-- Final source-scope consumers, preserving all initial418 sources.
@[default_target] lean_lib LebesgueDensityTrimming
@[default_target] lean_lib SourceLocalization
@[default_target] lean_lib LogarithmicTwoEndsAlgebra
@[default_target] lean_lib SourceLocalizationGeometry
@[default_target] lean_lib LogarithmicTwoEnds
@[default_target] lean_lib SixDimensionalLogarithmic
@[default_target] lean_lib WideLogarithmicTwoEnds
@[default_target] lean_lib LogarithmicLengthEstimates
@[default_target] lean_lib SixDimensionalLogarithmicLengths
