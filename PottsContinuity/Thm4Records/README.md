# `PottsContinuity/Thm4Records/`

Exploration records for the screen events of the proof of Theorem 4 and the connector factor.

32 modules, 3,321 lines. See [`PottsContinuity/OVERVIEW.md`](../OVERVIEW.md) for how the directories fit together.

| Module | Summary |
|---|---|
| [`ActualResidualConnector`](ActualResidualConnector.lean) | Declarations: `connectorNativeGraph`, `connectorNativeRead`, `connectorAuxiliaryDual`, `mem_connectorAuxiliaryDual`, … |
| [`ActualResidualConsumer`](ActualResidualConsumer.lean) | Declarations: `connectorRemainingRead`, `connectorRemainingNoncrossing`, `connectorRemainingRead_law`, `connectorRemainingNoncrossing_lower_of_no_primal_connections`, … |
| [`ActualSourceRecords`](ActualSourceRecords.lean) | Declarations: `connectorSourceEvent_readFrom_connectorReveal`, `SourceConnectorSurgery`, `slitScreenConnectorFactor_of_sourceSurgery` |
| [`AuxiliaryCrossing`](AuxiliaryCrossing.lean) | Declarations: `connectorCutCoreBase`, `ConnectorCutCoreVertex`, `connectorCutCoreSourceVertex`, `connectorCutCoreSource_adj`, … |
| [`AuxiliarySourceWalk`](AuxiliarySourceWalk.lean) | Declarations: `connectorRStarVertex_mem_middle`, `connectorRStarReadToSource`, `connectorAuxiliaryCrossing_source_walk` |
| [`CensoredOpenAttachment`](CensoredOpenAttachment.lean) | Declarations: `open_edge_endpoints_actualConnected`, `censoredSeedReveal_open_edge_endpoint_reached` |
| [`CentralFaceFreshness`](CentralFaceFreshness.lean) | Declarations: `crossedMiddleBond_mem_rStarSourceEdges`, `centralFace_crossedBond_unqueried` |
| [`CentralTraceSegment`](CentralTraceSegment.lean) | Declarations: `crossing_full_screens_central_segment` |
| [`ClusterFrontier`](ClusterFrontier.lean) | Declarations: `censoredSeedCluster_closed_under_open_adj`, `sideSeedConnection_readFrom_connectorReveal` |
| [`ConnectorFactor`](ConnectorFactor.lean) | Declarations: `slitScreenConnectorFactor` |
| [`ExteriorFreeze`](ExteriorFreeze.lean) | Declarations: `rStarSourceEdges`, `exteriorRevealEdges`, `connectorReveal`, `connectorReveal_stable`, … |
| [`FullTraceClip`](FullTraceClip.lean) | Declarations: `walk_between_full_trace_contacts`, `actual_connection_of_full_trace_segment` |
| [`LatticeBondBridge`](LatticeBondBridge.lean) | Declarations: `latticeAxisEquiv`, `latticeBondEquiv`, `latticeBondEquiv_source`, `latticeBondEquiv_target`, … |
| [`MaximalCompletion`](MaximalCompletion.lean) | Declarations: `sideOuterClusterReveal_subset_connectorReveal`, `sideOuterCluster_eq_of_connector_record` |
| [`NativeBoundaryOrder`](NativeBoundaryOrder.lean) | Declarations: `frozen_partition_le_wired_of_endpoint_attachment`, `connectorNativeVertex`, `connectorIncidentGraph`, `connectorNativeTopBottom`, … |
| [`NativeCoordinates`](NativeCoordinates.lean) | Declarations: `crossed_bond_endpoint_bounds`, `rStarSourceEdges_endpoint_bounds`, `source_edge_at_outer_column_queried`, `connectorNativeVertex_coordinates`, … |
| [`NativeIncidentConnectivity`](NativeIncidentConnectivity.lean) | Declarations: `openGraph_incidentRead_adj`, `openGraph_incidentRead_walk`, `actualConnected_incidentRead_of_ne`, `connectorBottomCluster`, … |
| [`NativeInteriorStar`](NativeInteriorStar.lean) | Declarations: `source_edge_interior_mem_rStarSourceEdges` |
| [`NativePartition`](NativePartition.lean) | Declarations: `ballQuery_no_native_attachment`, `connectorOpenQuery_native_endpoint_on_topBottom_of_no_primal_connections`, `connectorIncidentBoundary_le_topBottom_of_no_primal_connections`, `connectorIncidentNoncrossing_lower_of_no_primal_connections` |
| [`NativeReference`](NativeReference.lean) | Declarations: `connectorReferenceVertex`, `connectorReferenceGraph`, `connectorReferenceVertexMap`, `connectorReferenceEmbedding`, … |
| [`OuterClusterReveals`](OuterClusterReveals.lean) | Declarations: `sideWindow`, `sideCensoredGraph`, `sideCensoredGraph_le`, `sideOuterSeeds`, … |
| [`QueriedScreenIndex`](QueriedScreenIndex.lean) | Declarations: `queriedRStarEdge_side_query`, `sideQuery_face_exteriorIndex` |
| [`ResidualCarrier`](ResidualCarrier.lean) | Declarations: `recordedDualEdges`, `mem_recordedDualEdges` |
| [`ScreenIndex`](ScreenIndex.lean) | Declarations: `screenIndex_eq_of_uncrossed_adj`, `screenIndex_face_bottom_corners`, `screenIndex_face_left_corners`, `screenIndex_eq_of_dual_adj_off_trace`, … |
| [`Selection`](Selection.lean) | Declarations: `sideInnerVertices`, `sidePrimalConnectionEvent`, `SidePrimalDualAlternative`, `sidePrimalConnectionEvent_readFrom_connectorReveal`, … |
| [`SideCutSource`](SideCutSource.lean) | Declarations: `sideFaceBases`, `sideCutDual_endpoint_mem_faceBases`, `sideCutDual_actual_source_adj`, `sideCutDualToActualSource`, … |
| [`SideNativeAttachment`](SideNativeAttachment.lean) | Declarations: `sideOuterCluster_subset_sideWindow`, `source_edge_eq_pair_of_endpoints`, `sideOpenQuery_no_native_attachment_of_no_primal_connection` |
| [`SideRectangle`](SideRectangle.lean) | Declarations: `sideRectangleBase`, `SideRectangleVertex`, `sideRectangleSourceVertex`, `sideRectangleSourceEmbedding`, … |
| [`SideRectangleRead`](SideRectangleRead.lean) | Declarations: `sideRectangleSource_graph_le`, `sideRectangleConfiguration`, `sideRectangleVertexOfSource`, `sideRectangleSourceVertex_vertexOfSource`, … |
| [`SourceConnectorSurgery`](SourceConnectorSurgery.lean) | Declarations: `connectorAuxiliaryCrossing_implies_sourceConnector`, `sourceConnectorSurgery` |
| [`SourceScreenIndex`](SourceScreenIndex.lean) | Declarations: `sourceScreenIndexWalk`, `sourceScreenIndexWalk_support`, `sourceScreenIndexWalk_edges`, `sourceOpenStep_avoids_sourceScreen`, … |
| [`TraceInterior`](TraceInterior.lean) | Declarations: `path_interior_covers_edges`, `walk_between_full_traces_with_interior` |
