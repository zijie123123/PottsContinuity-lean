# `PottsContinuity/BD12/`

The value p_c(q) = sqrt(q)/(1 + sqrt q) for q >= 1 (from [BD12a], by the sharp-threshold method of Duminil-Copin-Raoufi-Tassion) and crossing estimates at p_c (Theorem 9).

224 modules, 14,549 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`ActiveHybridCovariance`](ActiveHybridCovariance.lean) | The covariance estimate with the actual stopping-aware selected edge. |
| [`ActiveHybridStopping`](ActiveHybridStopping.lean) | Adjacent actual hybrids agree off the active original-query event. |
| [`ActiveOriginalQuery`](ActiveOriginalQuery.lean) | The original adaptive query made strictly before the observable has been determined. |
| [`ActiveQueryCostAverage`](ActiveQueryCostAverage.lean) | Average the selected-query covariance estimate over the actual original prefix. |
| [`ActiveQueryRegularity`](ActiveQueryRegularity.lean) | Measurability of the actual stopping-aware adaptive query. |
| [`ActiveQueryRevealment`](ActiveQueryRevealment.lean) | Identify the time sum of active-query probabilities with the actual event that the exploration queries an edge. |
| [`AdaptiveHybridQuery`](AdaptiveHybridQuery.lean) | The edge selected at a given adaptive exploration time, and the literal hybrid bit there. |
| [`AdaptiveRevealStrategy`](AdaptiveRevealStrategy.lean) | Complete reveal trees obtained from literal fresh-edge selection strategies. |
| [`AugmentedUniformTree`](AugmentedUniformTree.lean) | Adaptive reveal orders may depend on past full uniform values and on an auxiliary sequence, rather than only the revealed Boolean answers. |
| [`BoundaryComponentCost`](BoundaryComponentCost.lean) | Boundary wiring changes the number of components by at most the number of boundary vertices, uniformly over all actual edge configurations. |
| [`BoundaryMergeComparison`](BoundaryMergeComparison.lean) | Declarations: `boundaryMerge`, `componentSetoid_merge`, `openGraph_singleEdge_reachableSetoid_eq_wired`, `boundaryConditionOfSetoid`, … |
| [`BoundaryPressureCost`](BoundaryPressureCost.lean) | Uniform surface bounds for actual finite FK partition functions. |
| [`BoundedVarianceDistance`](BoundedVarianceDistance.lean) | The independent-copy variance bound and the elementary finite telescoping estimate used before the OSSS revealment sum. |
| [`BoxCentredOneArmComparison`](BoxCentredOneArmComparison.lean) | A restricted centred one-arm event uses genuine original outer edges. |
| [`BoxEdgeOrder`](BoxEdgeOrder.lean) | Canonical endpoint ordering of original box edges, by lexicographic order of the actual integer coordinates. |
| [`BoxEdgePressureBridge`](BoxEdgePressureBridge.lean) | Actual finite-box edge means and their infinite-volume comparisons. |
| [`BoxInnerPartition`](BoxInnerPartition.lean) | Canonical inner/outer closed-box edge partition and literal restriction. |
| [`BoxOneArmTranslation`](BoxOneArmTranslation.lean) | Translation of the actual centred one-arm observable and its homogeneous wired finite-box probability. |
| [`BoxRadiusData`](BoxRadiusData.lean) | The exact metric data on every finite closed lattice box, including its centre and isolated vertices. |
| [`BoxRadiusRestriction`](BoxRadiusRestriction.lean) | First-radius-hit equality on actual nested lattice boxes. |
| [`ClusterFrontier`](ClusterFrontier.lean) | The boundary-seed exploration frontier and its literal least-ranked fresh edge. |
| [`CriticalUpperBound`](CriticalUpperBound.lean) | The genuine threshold is at most the explicit self-dual point, for every real q>=1. |
| [`CriticalValue`](CriticalValue.lean) | The explicit self-dual value is the genuine frozen threshold for every real q at least one. |
| [`CriticalValueConditional`](CriticalValueConditional.lean) | Genuine-threshold identification assembled from the two independent interfaces. |
| [`DRTAssociation`](DRTAssociation.lean) | FKG and the corrected Russo lower bound for the finite weighted DRT law. |
| [`DRTBoxArmMaximum`](DRTBoxArmMaximum.lean) | Compare the restricted inner-path denominator with full outer centred one-arm sums under the same original finite FK law. |
| [`DRTBoxDifferential`](DRTBoxDifferential.lean) | The finite-box DRT differential estimate with all metric, partition, endpoint and first-hit inputs discharged. |
| [`DRTBoxHomogeneous`](DRTBoxHomogeneous.lean) | Homogeneous finite-box differential inequality with a positive coefficient uniform on a bounded inverse-temperature interval. |
| [`DRTBoxOuterDifferential`](DRTBoxOuterDifferential.lean) | Finite-box differential inequality with the full outer centred one-arm maximum, as required before comparison with translated wired domains. |
| [`DRTCentredSmallScale`](DRTCentredSmallScale.lean) | The actual small-scale wired comparison in DRT: centred one-arm events in Lambda_2n are bounded by the source theta_k whenever 2k<=n. |
| [`DRTConditionalAssociation`](DRTConditionalAssociation.lean) | Conditional FKG and one-step conditional monotonicity for the actual finite DRT weights, with arbitrary revealed edges and arbitrary … |
| [`DRTEventProbability`](DRTEventProbability.lean) | Actual finite event probabilities as means under the homogeneous beta-law. |
| [`DRTExponentialGrowth`](DRTExponentialGrowth.lean) | The integrating-factor step of DRT's scalar sharpness bootstrap. Honest pointwise derivative bounds imply an exponential bound between two … |
| [`DRTFiniteLaw`](DRTFiniteLaw.lean) | Finite weighted FK law in the DRT inverse-temperature parameter. The unnormalized expression is analytic for every real argument. |
| [`DRTGenuineSubcriticalSharpness`](DRTGenuineSubcriticalSharpness.lean) | Exponential decay of the actual finite wired one-arm sequence throughout the subcritical interval of the frozen genuine threshold. |
| [`DRTHalvingSum`](DRTHalvingSum.lean) | Exact multiplicity bound for integer halving in the source partial-sum comparison, with the radius-zero term retained. |
| [`DRTHomogeneousBridge`](DRTHomogeneousBridge.lean) | The homogeneous DRT law is exactly the existing finite FK law at p = 1-exp(-beta), not an alternative notion of random-cluster measure. |
| [`DRTHomogeneousIsomorphism`](DRTHomogeneousIsomorphism.lean) | Relabelling invariance of every observable under the actual homogeneous finite beta-law, with the boundary partition transported exactly. |
| [`DRTHomogeneousParameters`](DRTHomogeneousParameters.lean) | The actual homogeneous physical parameter map beta -> 1-exp(-beta), including equality of the finite laws and of every finite observable's … |
| [`DRTHybridFirstCross`](DRTHybridFirstCross.lean) | The first integrated hybrid cross bound for the actual finite weighted FK law, with all q>=1, positive couplings, beta and boundary … |
| [`DRTInnerCovariance`](DRTInnerCovariance.lean) | The inner-shell covariance estimate under an actual outer finite FK law, for all real q>=1 and arbitrary outer boundary partitions and … |
| [`DRTInnerDifferential`](DRTInnerDifferential.lean) | The inner-shell covariance estimate under an actual outer finite FK law, for all real q>=1 and arbitrary outer boundary partitions and … |
| [`DRTInverseTemperature`](DRTInverseTemperature.lean) | Explicit inverse of the homogeneous physical probability map on every interior FK parameter record. |
| [`DRTLogActivity`](DRTLogActivity.lean) | Log edge activity parametrizes all physical homogeneous temperatures. |
| [`DRTLogAverageLimit`](DRTLogAverageLimit.lean) | Convergence of DRT's logarithmically normalized averages. |
| [`DRTLogPartialSum`](DRTLogPartialSum.lean) | The finite logarithmic telescoping bound in DRT's scalar technical lemma. |
| [`DRTMeanBetaMonotone`](DRTMeanBetaMonotone.lean) | Monotonicity in inverse temperature for increasing finite observables, derived from the actual corrected derivative and finite positive … |
| [`DRTMeanOrder`](DRTMeanOrder.lean) | Order properties of expectations under the actual finite weighted FK law. |
| [`DRTPartialSumDecay`](DRTPartialSumDecay.lean) | The partial sums Sigma_n(beta) in DRT's technical scalar lemma. |
| [`DRTPressureDerivative`](DRTPressureDerivative.lean) | The pressure derivative for the actual weighted FK partition function. |
| [`DRTRadiusSum`](DRTRadiusSum.lean) | The factor-two shell-radius counting step in DRT's corollary of the OSSS inequality. |
| [`DRTRusso`](DRTRusso.lean) | The corrected weighted finite-graph Russo identity, expanded edge by edge. |
| [`DRTRussoCorrection`](DRTRussoCorrection.lean) | The coefficient of the DRT Russo formula. The derivative formula displayed in the proof of Theorem 1.2 of arXiv:1705.03104v2 has the … |
| [`DRTSourceDenominator`](DRTSourceDenominator.lean) | The actual source bound M<=2*S_n under the wired Lambda_2n law. |
| [`DRTStretchedSummable`](DRTStretchedSummable.lean) | Summability of stretched exponential tails, used in the first-to-second stage of the DRT scalar bootstrap. |
| [`DRTStrictMean`](DRTStrictMean.lean) | Strict upper bounds for actual finite expectations from a configuration of strictly positive weight on which the observable is below one. |
| [`DRTWeightedAverageLimit`](DRTWeightedAverageLimit.lean) | Weighted averages of convergent real sequences and the logarithmic normalization used in DRT's mean-field argument. |
| [`DRTWiredBoxTranslation`](DRTWiredBoxTranslation.lean) | Translation of arbitrary finite observables under actual homogeneous wired box laws, using the shared exact boundary-partition transport. |
| [`DRTWiredExponentialBootstrap`](DRTWiredExponentialBootstrap.lean) | The two-stage DRT bootstrap for the actual wired one-arm sequence. |
| [`DRTWiredInfiniteArmBound`](DRTWiredInfiniteArmBound.lean) | Infinite wired shell probabilities are bounded by the actual finite source theta_n, by domain comparison and fixed-cylinder convergence. |
| [`DRTWiredIntegratedGrowth`](DRTWiredIntegratedGrowth.lean) | Integrated differential inequality for the actual finite wired sequence. |
| [`DRTWiredLogAverageDerivative`](DRTWiredLogAverageDerivative.lean) | The averaged derivative estimate for the actual wired sequence in DRT. |
| [`DRTWiredLogAverageIntegrated`](DRTWiredLogAverageIntegrated.lean) | Integration of the actual averaged growth bound on a positive interval. |
| [`DRTWiredLogGrowthZero`](DRTWiredLogGrowthZero.lean) | A zero actual one-arm limit forces logarithmically sublinear partial sums at every smaller positive parameter. |
| [`DRTWiredOneArmExpression`](DRTWiredOneArmExpression.lean) | The explicit finite quotient as a real function for differentiation. |
| [`DRTWiredOneArmSequence`](DRTWiredOneArmSequence.lean) | The actual finite wired one-arm sequence and its source partial sums. |
| [`DRTWiredOneArmUpper`](DRTWiredOneArmUpper.lean) | A uniform strict upper bound for the actual finite wired one-arm sequence. |
| [`DRTWiredSharpnessFromZero`](DRTWiredSharpnessFromZero.lean) | Sharpness of the finite wired sequence below an upper parameter with zero one-arm limit. |
| [`DRTWiredSourceDifferential`](DRTWiredSourceDifferential.lean) | DRT's finite wired source differential inequality with its actual partial sum denominator. |
| [`DRTWiredSourceGrowth`](DRTWiredSourceGrowth.lean) | DRT's actual finite wired growth inequality, with a strictly positive coefficient uniform below a fixed positive inverse temperature. |
| [`DRTWiredStretchedDecay`](DRTWiredStretchedDecay.lean) | The first bootstrap stage for the actual wired sequence: a sublinear power bound on its genuine partial sums yields a summable … |
| [`DRTWiredZeroLimit`](DRTWiredZeroLimit.lean) | The actual finite wired one-arm sequence vanishes whenever its frozen infinite-volume wired limit has no infinite origin cluster. |
| [`DualParameterOrder`](DualParameterOrder.lean) | Order reversal of physical dual parameters, independent of threshold claims. |
| [`DualStrip`](DualStrip.lean) | Contracting the dangling side ports of the true rectangle dual. The projection clamps the horizontal coordinate to the strip between the … |
| [`DualStripOpen`](DualStripOpen.lean) | True-dual port crossings give ordinary vertical strip crossings. |
| [`EmbeddedOpenRestriction`](EmbeddedOpenRestriction.lean) | Original open edges under an embedded finite graph restriction. |
| [`EmbeddingPartition`](EmbeddingPartition.lean) | Coordinate partition induced by an injection. |
| [`FiniteDomainOneArm`](FiniteDomainOneArm.lean) | Literal finite one-arm events on arbitrary induced lattice domains. |
| [`FiniteDomainOneArmRestriction`](FiniteDomainOneArmRestriction.lean) | A one-arm event is determined inside any induced subdomain containing the entire target-radius ball, independently of the exterior … |
| [`FiniteMonotoneSampler`](FiniteMonotoneSampler.lean) | The deterministic sequential threshold sampler used in DRT. |
| [`FiniteOSSS`](FiniteOSSS.lean) | Finite monotone-measure OSSS for an actual stopping reveal tree and its usual revealment probability. |
| [`FiniteOSSSQuerySum`](FiniteOSSSQuerySum.lean) | Finite monotone-measure OSSS with literal active-query probabilities summed by time. |
| [`FinitePinnedAssociation`](FinitePinnedAssociation.lean) | Finite conditional FKG for positive weights on the Boolean cube. |
| [`FinitePinnedClosedUpdate`](FinitePinnedClosedUpdate.lean) | Closed-coordinate conditioning and the conditional open/closed comparison used by a monotone adaptive sampler. |
| [`FinitePinnedLaw`](FinitePinnedLaw.lean) | The genuine conditional PMF corresponding to finitePinnedMean. |
| [`FinitePinnedMonotonicity`](FinitePinnedMonotonicity.lean) | Revealing an open coordinate increases every increasing nonnegative observable under a positive log-supermodular finite Boolean law. |
| [`FinitePinnedPattern`](FinitePinnedPattern.lean) | Monotonicity in every revealed coordinate, rather than just a single open/closed comparison. |
| [`FinitePressureEdgeSandwich`](FinitePressureEdgeSandwich.lean) | A cross-parameter edge-count comparison with the actual FK surface error. |
| [`FiniteRevealKernel`](FiniteRevealKernel.lean) | Exact one-edge disintegration of the pinned finite law. |
| [`FiniteRevealTree`](FiniteRevealTree.lean) | Adaptive finite reveal trees and their exact output law. |
| [`FiniteSeedWindow`](FiniteSeedWindow.lean) | An explicit finite independent seed space, represented as streams with a prescribed background outside the sampled time window. |
| [`FiniteUniformReveal`](FiniteUniformReveal.lean) | Realization of the actual fresh-edge conditional kernel by an independent uniform threshold, with no abstract sampling-law assumption. |
| [`FiniteUniformTree`](FiniteUniformTree.lean) | The actual fresh-uniform adaptive tree sampler. |
| [`FiniteWeightDerivative`](FiniteWeightDerivative.lean) | Finite product and normalization derivatives used by the corrected DRT formula. |
| [`FiniteWiredOneArmComparison`](FiniteWiredOneArmComparison.lean) | Wired one-arm comparison on nested induced domains containing the full radius ball. |
| [`FiniteWiredRestriction`](FiniteWiredRestriction.lean) | Wired domain comparison for every increasing event on a finite induced lattice graph, beyond the all-open-cylinder specialization of shared … |
| [`FixedOriginalHybridLaw`](FixedOriginalHybridLaw.lean) | Identification of the actual finite-V-product hybrid family with its fully fixed-original-input seed kernel. |
| [`FixedOriginalHybridMoments`](FixedOriginalHybridMoments.lean) | Observable moments transferred between the actual finite replacement product space and the fully fixed-original seed kernel, followed by … |
| [`FixedOriginalHybridRegularity`](FixedOriginalHybridRegularity.lean) | Measurability of fixed-U hybrid moments and the exact mean of the replaced selected bit. |
| [`FixedOriginalSeedExtension`](FixedOriginalSeedExtension.lean) | Pair-valued finite seed insertion with the original U inputs prescribed and the replacement V inputs supplied by a finite vector. |
| [`FixedOriginalSeedProduct`](FixedOriginalSeedProduct.lean) | The fully fixed-original-input seed law is the pushforward of an actual finite product of independent replacement uniforms. |
| [`GraphInnerPartition`](GraphInnerPartition.lean) | The canonical edge partition of an embedded graph. |
| [`HarrisFiniteProduct`](HarrisFiniteProduct.lean) | Harris association for every finite product of real probability laws, in particular the independent uniforms in DRT's hybrid coupling. |
| [`HarrisOneDimensional`](HarrisOneDimensional.lean) | One-dimensional Harris association, the base case for the product-uniform FKG inequality needed in DRT's hybrid coupling. |
| [`HarrisTensorization`](HarrisTensorization.lean) | Positive association is preserved by independent products. |
| [`HybridFamilyEvaluation`](HybridFamilyEvaluation.lean) | Deterministic evaluation retaining X and a finite family of hybrids, and its dependence only on not-yet-used seed coordinates. |
| [`HybridFamilyKernel`](HybridFamilyKernel.lean) | A shared original-coordinate (U,V) kernel for any finite family of DRT hybrids. |
| [`HybridFiberSampler`](HybridFiberSampler.lean) | The stopped-hybrid fiber algorithm from DRT, conditional on a prescribed initial segment of the original U inputs. |
| [`HybridPairMoments`](HybridPairMoments.lean) | Measurability and bounds for actual joint moments of two hybrid cutoffs. |
| [`HybridPairSeedIntegral`](HybridPairSeedIntegral.lean) | Transfer joint hybrid observables between the two independent input fields and the common paired seed law used by the variance telescoping … |
| [`HybridQueryCoordinate`](HybridQueryCoordinate.lean) | The actual switched coordinate does not depend on the continuation of the original exploration. |
| [`HybridSeedIdentification`](HybridSeedIdentification.lean) | Identification of the common-stream deterministic DRT construction with its shared original-coordinate kernel. |
| [`HybridSeedMoments`](HybridSeedMoments.lean) | Actual common-space hybrid moments under fixed original prefixes, now obtained from the proved joint seed/kernel identification. |
| [`HybridVarianceTelescoping`](HybridVarianceTelescoping.lean) | DRT's variance-to-hybrid-increment reduction on the actual common seed space. |
| [`IndependentKernelProduct`](IndependentKernelProduct.lean) | Independent kernel tensorization for finite output spaces. |
| [`InducedOpenRestriction`](InducedOpenRestriction.lean) | Literal induced-subgraph restriction of a sampled finite configuration. |
| [`InfiniteBoxPressureSandwich`](InfiniteBoxPressureSandwich.lean) | Summed infinite-volume intensities inherit the actual finite surface error. |
| [`InfiniteFinitePatternPositive`](InfiniteFinitePatternPositive.lean) | Every prescribed finite all-open pattern has positive probability under the actual frozen free and wired limits at interior parameters. |
| [`InfiniteRadiusEvent`](InfiniteRadiusEvent.lean) | Whole-plane radius-shell events and their literal finite restrictions. |
| [`InfiniteRadiusLimit`](InfiniteRadiusLimit.lean) | Decreasing shell events recover the actual infinite open cluster and its probability by continuity from above. |
| [`InfiniteRadiusTranslation`](InfiniteRadiusTranslation.lean) | Literal translation of shell events and their wired infinite-volume probabilities. |
| [`InfiniteRectangleEvents`](InfiniteRectangleEvents.lean) | Actual finite rectangle observables of whole-plane configurations. Restriction retains exactly the open sampled bonds. |
| [`IntegralFourTerms`](IntegralFourTerms.lean) | Linear integration of a four-term identity on an almost-everywhere fibre. |
| [`JointHybridAssociation`](JointHybridAssociation.lean) | Harris association for the actual common-space hybrids, with original U fixed. |
| [`JointHybridEvaluation`](JointHybridEvaluation.lean) | DRT's original sample and all stopped hybrids on one common pair of seed streams. |
| [`JointHybridRegularity`](JointHybridRegularity.lean) | Measurability and replacement-seed monotonicity of the common-space DRT hybrids. |
| [`JointHybridSwitch`](JointHybridSwitch.lean) | The DRT switch identity for the actual adaptive hybrid continuation. |
| [`KSTApproximation`](KSTApproximation.lean) | Compact approximation for the KST measurable FKG hypothesis. A copy of the finite upper hull, compact separation, clopen approximation and … |
| [`KSTArmCoverDualLimit`](KSTArmCoverDualLimit.lean) | The probability consequence of the exact half-cell dual arm certificate. |
| [`KSTArmCoverExport`](KSTArmCoverExport.lean) | The exact KST arm bound for both actual FK boundary limits at the explicit self-dual parameter. |
| [`KSTBothBoundaryHypotheses`](KSTBothBoundaryHypotheses.lean) | KST probability hypotheses for either frozen infinite-volume boundary condition. |
| [`KSTBridgeCoverExport`](KSTBridgeCoverExport.lean) | The finite bridge cover of `PlanarTopology.KSTBridgeFiniteCover`, applied to the actual wired limit. |
| [`KSTBridgePositive`](KSTBridgePositive.lean) | Positive probability of a literal KST bridge, witnessed by the horizontal path along the top boundary and the finite-energy property. |
| [`KSTCascade`](KSTCascade.lean) | Actual wired-law cascade and closing, conditional on the remaining deterministic inclusions. |
| [`KSTCascadeExport`](KSTCascadeExport.lean) | KST's wired cascade with the corridor geometry of `PlanarTopology.KSTCascadeInclusion` discharged at integral scales divisible by twelve. |
| [`KSTConstructionExport`](KSTConstructionExport.lean) | The six-event KST probability construction, with the exact geometry `PlanarTopology.kst_quasi_construction` consumed. |
| [`KSTCoverTransform`](KSTCoverTransform.lean) | The explicit finite-cover transform in KST's first relation. |
| [`KSTCoverTransformOrder`](KSTCoverTransformOrder.lean) | Endpoint, order and continuity facts for KST's explicit cover transform. |
| [`KSTEventRegularity`](KSTEventRegularity.lean) | Measurability and monotonicity of the actual KST path events. |
| [`KSTEvents`](KSTEvents.lean) | The path events used by KST. Integer inequalities express the source's rational target widths exactly. |
| [`KSTFiniteAssociation`](KSTFiniteAssociation.lean) | Finite FKG products for KST construction and finite-cover gluing. |
| [`KSTHypotheses`](KSTHypotheses.lean) | KST probabilistic hypotheses for the wired law. The positively associated events here are arbitrary measurable upper events. |
| [`KSTProbability`](KSTProbability.lean) | The probability part of KST's cascading and closing relations. |
| [`KSTScaleInterpolation`](KSTScaleInterpolation.lean) | Geometric-scale selection for the source integral KST sequence. |
| [`KSTScales`](KSTScales.lean) | Integral source scales used by the shared KST corridor construction. |
| [`KSTUniformScaleInduction`](KSTUniformScaleInduction.lean) | The numerical uniform-scale induction in KST: adjacent quasi-crossings, cascade and closing transport a positive base bridge to every … |
| [`KSTUniformWiredBridge`](KSTUniformWiredBridge.lean) | Uniform KST bridge bounds from actual adjacent quasi-crossings. |
| [`KSTWiredConstructionInputs`](KSTWiredConstructionInputs.lean) | Uniform lower bounds on the six actual wired KST construction inputs at self-dual parameters. |
| [`KSTWiredSelfDualUniform`](KSTWiredSelfDualUniform.lean) | Actual wired uniform bridge and aspect-eight crossing bounds at the explicit self-dual parameter. |
| [`LatticeBoxContainment`](LatticeBoxContainment.lean) | Exact translated-box containments used in the wired-domain comparison. |
| [`LatticeRadius`](LatticeRadius.lean) | Integer sup-radius of actual square-lattice vertices. |
| [`MarginalCovariance`](MarginalCovariance.lean) | Expectations, covariances and actual exploration OSSS transferred from a true coordinate marginal to the original outer law. |
| [`MarginalCovarianceSum`](MarginalCovarianceSum.lean) | Adding the unrevealed outer edges to a covariance sum is legitimate: FKG makes every added covariance nonnegative under the original law. |
| [`OneArmIsomorphism`](OneArmIsomorphism.lean) | One-arm observables transported by an actual graph isomorphism preserving the supplied integer radius functions. |
| [`OptionQueryIntegral`](OptionQueryIntegral.lean) | Integrate weights attached to the edge returned by a finite optional query. |
| [`OrderedEdgeMarginalUniqueness`](OrderedEdgeMarginalUniqueness.lean) | Stochastic order and equality of single-edge intensities imply equality of the whole laws. |
| [`OriginalEvalMoments`](OriginalEvalMoments.lean) | Moments of the actual original adaptive sample under its independent uniform inputs. |
| [`OriginalPinBlock`](OriginalPinBlock.lean) | Independent original-input blocks and their exact disintegration into the fixed-prefix seed kernels. |
| [`OriginalPinBlockIntegralRecursion`](OriginalPinBlockIntegralRecursion.lean) | Declarations: `finiteOriginalPinBlock_integral_succ` |
| [`OriginalPinBlockSplit`](OriginalPinBlockSplit.lean) | Exact decomposition of an original uniform block into consecutive prefix and suffix blocks. |
| [`OriginalPinBlockTower`](OriginalPinBlockTower.lean) | Integral towers and past-coordinate preservation for original-input blocks. |
| [`PartitionCentredCovariance`](PartitionCentredCovariance.lean) | DRT's inner exploration covariance bound under a true larger-cube law. |
| [`PartitionCovarianceAllEdges`](PartitionCovarianceAllEdges.lean) | DRT's inner exploration covariance bound under a true larger-cube law. |
| [`PositiveCentredCovariance`](PositiveCentredCovariance.lean) | The positive finite centred one-arm covariance-sum estimate, with all exploration and counting steps proved. |
| [`PositiveCentredOneArmSum`](PositiveCentredOneArmSum.lean) | Compare actual shell sums to centred one-arm sums by radius differences. |
| [`PositiveMarginal`](PositiveMarginal.lean) | A true marginal of a positive Boolean-cube weight. |
| [`PositiveMean`](PositiveMean.lean) | Means and covariances of strictly positive finite weights, including true inner-edge marginals, without requiring the marginal itself to be … |
| [`PositiveOneArmComparison`](PositiveOneArmComparison.lean) | One-arm comparisons for arbitrary positive finite laws, in particular true marginals of larger-domain random-cluster laws. |
| [`PositiveSeedConnectionOSSS`](PositiveSeedConnectionOSSS.lean) | Positive-weight connection OSSS with the seed exploration's endpoint-connection revealment estimates proved. |
| [`PositiveShellAverageOSSS`](PositiveShellAverageOSSS.lean) | Average the actual boundary-seed explorations over shells 1,...,n. |
| [`PositiveShellConnectionMaximum`](PositiveShellConnectionMaximum.lean) | The finite sum and genuine maximum of endpoint-to-shell connection probabilities used when averaging DRT's boundary-seed explorations. |
| [`PressureDerivativeSandwich`](PressureDerivativeSandwich.lean) | A finite surface error controls derivatives at separated parameters. |
| [`ProbabilityKernelBind`](ProbabilityKernelBind.lean) | Probability kernel identities for finite-prefix disintegration. |
| [`ProbabilityKernelIntegral`](ProbabilityKernelIntegral.lean) | Bounded real observable integrals for measurable probability kernels. |
| [`QueryNoRepetition`](QueryNoRepetition.lean) | Actual reveal trees query only fresh edges, hence each edge at most once. |
| [`RadiusOneArmComparison`](RadiusOneArmComparison.lean) | Graph-metric comparison between a connection to a global shell and a centred one-arm event. |
| [`RectangleBoxComparison`](RectangleBoxComparison.lean) | Literal rectangle observables and finite wired-box comparison. |
| [`RectangleConfinedWalk`](RectangleConfinedWalk.lean) | Horizontal crossings as actual whole-plane open walks confined to the literal rectangle. |
| [`RectangleHeightMonotone`](RectangleHeightMonotone.lean) | Enlarging only the height preserves an actual horizontal crossing, which gives the easy-direction rectangle bound from the wired square … |
| [`RectangleOpenGraphs`](RectangleOpenGraphs.lean) | Open-graph bridges for finite restrictions of whole-plane states. |
| [`RectanglePositive`](RectanglePositive.lean) | Every finite actual rectangle crossing has positive probability at an interior FK parameter, witnessed by the open bottom horizontal path. |
| [`RectangleSymmetry`](RectangleSymmetry.lean) | Affine diagonal symmetry taking the dual strip to the primal rectangle. |
| [`RectangleTranslation`](RectangleTranslation.lean) | Literal translation of actual confined rectangle crossings and their wired infinite-volume probabilities. |
| [`RectangleWidthTruncation`](RectangleWidthTruncation.lean) | First-hit truncation in the horizontal coordinate narrows a rectangle crossing while retaining the original lower-left side and vertical … |
| [`ReindexedMarginal`](ReindexedMarginal.lean) | Canonical marginalisation along any finite coordinate partition. |
| [`ReverseCriticalLower`](ReverseCriticalLower.lean) | Reverse genuine-threshold assembly with separate coincidence and planar inputs. |
| [`ReverseThresholdContracts`](ReverseThresholdContracts.lean) | Explicit independent inputs to the reverse genuine-threshold assembly. |
| [`SeedClusterQuerySupport`](SeedClusterQuerySupport.lean) | Every active query of the concrete seed exploration touches an actual seed cluster in the final sampled configuration. |
| [`SeedClusterRevealTree`](SeedClusterRevealTree.lean) | Literal adaptive boundary-seed cluster exploration. |
| [`SeedClusterRevealment`](SeedClusterRevealment.lean) | The actual boundary-seed exploration revealment is bounded by endpoint connection probabilities under the original positive-weight law. |
| [`SeedMediatedConnection`](SeedMediatedConnection.lean) | The connection event witnessed through a seed vertex, and its exact determination once all edges incident to the discovered seed clusters … |
| [`SeedWindowCongruence`](SeedWindowCongruence.lean) | Exact dependence of finite independent seed windows on their original-input laws. |
| [`SeedWindowMeasurability`](SeedWindowMeasurability.lean) | Measurability of the actual fixed-prefix seed law, including its dependence on the prescribed original inputs. |
| [`SeedWindowPinTower`](SeedWindowPinTower.lean) | Exact finite-prefix tower identity: averaging the newly pinned original coordinate recovers the preceding fixed-prefix seed law. |
| [`SelectedHybridBitPrefix`](SelectedHybridBitPrefix.lean) | The actual selected-edge hybrid bits depend on the short original prefixes used by DRT. |
| [`SelectedHybridCovariance`](SelectedHybridCovariance.lean) | The actual adjacent-hybrid switch cost is bounded by twice the original covariance at the adaptively selected edge. |
| [`SelectedHybridFirstCross`](SelectedHybridFirstCross.lean) | The first integrated Harris cross term in DRT's covariance switch estimate: the replaced selected bit has its original-law mean pointwise … |
| [`SelectedHybridSecondCross`](SelectedHybridSecondCross.lean) | The second integrated Harris cross term, using the two-stage original-input average of the actual separate replacement-input expectations. |
| [`SelectedHybridSecondProduct`](SelectedHybridSecondProduct.lean) | The product of separate V-expectations in the second Harris cross term. |
| [`SelectedHybridSwitch`](SelectedHybridSwitch.lean) | The four-term adjacent-hybrid identity at an arbitrary adaptive query time. |
| [`SelfDualRectangle`](SelfDualRectangle.lean) | Actual rectangle duality at the formula value. Specializes the proved free/wired finite-law transport to the self-dual point. |
| [`SelfDualSourceArmBound`](SelfDualSourceArmBound.lean) | Polynomial lower bound for the actual finite source one-arm sequence at the explicit self-dual parameter, every real q>=1. |
| [`SeparatingSeedConnection`](SeparatingSeedConnection.lean) | A path-separating seed set makes the seed-mediated observable exactly the ordinary connection-to-target indicator, on every configuration. |
| [`SeparatingSeedRevealment`](SeparatingSeedRevealment.lean) | Ordinary connection-event revealments from the actual seed exploration. |
| [`SquareOneArmBound`](SquareOneArmBound.lean) | A square crossing starts a radius-n arm at one of its n+1 left-side vertices. |
| [`StoppingDetermination`](StoppingDetermination.lean) | The actual stopping predicate for a finite decision tree: the revealed coordinates determine the observable on their entire configuration … |
| [`TerminalHybridIndependence`](TerminalHybridIndependence.lean) | The all-replacement terminal hybrid is independent of the original output in the actual common-input coupling, even though its reveal order … |
| [`ThresholdInterfaces`](ThresholdInterfaces.lean) | The independent inputs to genuine-threshold identification are discharged. |
| [`TwoBlockBoundaryMerge`](TwoBlockBoundaryMerge.lean) | Declarations: `twoBlockSetoid`, `twoBlockSetoid_eq_sup`, `twoBlockBoundary`, `twoBlockBoundary_partition_rel`, … |
| [`TwoBlockConnectivity`](TwoBlockConnectivity.lean) | Actual connection between separately wired arcs. For BD12 Lemma self-duality, boundary identifications are used in the weight, whereas the … |
| [`UniformThreshold`](UniformThreshold.lean) | The literal uniform-threshold realization of a Boolean probability, including both endpoints. |
| [`WalkRadiusLevel`](WalkRadiusLevel.lean) | Integer-radius intermediate values along graph walks. |
| [`WalkRadiusPrefix`](WalkRadiusPrefix.lean) | Stop a walk at its first visit to an integer radius level. |
| [`WeakRSWFiniteBox`](WeakRSWFiniteBox.lean) | Wired RSW in every finite box containing the entire translated rectangle. |
| [`WeakRSWSelfDual`](WeakRSWSelfDual.lean) | Wired RSW for every real aspect bound at the explicit self-dual point. |
| [`WholePlaneDuality`](WholePlaneDuality.lean) | Whole-plane duality with every-exhaustion hypotheses. These statements consume the frozen limit predicate, using its box specialization … |
| [`WholePlaneRectangleDuality`](WholePlaneRectangleDuality.lean) | Exact rectangle complement identity for arbitrary whole-plane states. |
| [`WiredArcRemoval`](WiredArcRemoval.lean) | Removing prewired edges preserves actual arc-connection probability. Boundary-internal edges need not be preserved by reflected duality. |
| [`WiredAspectTwoAllScales`](WiredAspectTwoAllScales.lean) | The actual wired aspect-two crossing bound at every integer height. |
| [`WiredBoxRadiusIdentity`](WiredBoxRadiusIdentity.lean) | Exact shell-event probabilities under wired extension when the target ball is contained in the sampled box. |
| [`WiredBoxRadiusProbability`](WiredBoxRadiusProbability.lean) | Finite actual one-arm probabilities are bounded by fixed-radius cylinders under their literal wired whole-plane extensions. |
| [`WiredEvenAspectBounds`](WiredEvenAspectBounds.lean) | Wired crossings at every integer aspect ratio and every even height. |
| [`WiredIntegerAspectBounds`](WiredIntegerAspectBounds.lean) | Every integer aspect bound at every positive integer height, including odd and unit heights. |
| [`WiredSquare`](WiredSquare.lean) | Wired square crossing bound at the self-dual formula. Whole-plane duality, free-to-wired comparison and an affine diagonal symmetry give … |
