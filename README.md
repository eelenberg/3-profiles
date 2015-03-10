# 3-Profile Readme

## 3profileLocal

Local 3-profile Counting.

Given an undirected graph, this program computes the frequencies of all subgraphs on 3 vertices (up to isomorphism). A file counts_3_profiles.txt is appended with input filename, edge sampling probability, 3-profile of the graph, and runtime. Network traffic is appended to netw_counts_3_profiles.txt similarly. An option (per_vertex) is also provided which writes the local 3-profile, for each vertex the count of subgraphs including that vertex. The algorithm assumes that each undirected edge appears exactly once in the graph input. If edges may appear more than once, this procedure will over count.

	./3profileLocal --graph mygraph.txt --format tsv --sample_iter 10 --min_prob .5 --max_prob 1 --prob_step .1
	./3profileLocal --graph mygraph.txt --format tsv --per_vertex local3


## 3profileEgoSer

Ego 3-profile Counting (serial).

Given an undirected graph, this program computes the global 3-profile for a specified list of ego subgraphs (id_list). For vertex id in the input list, the serial algorithm computes the ego subgraph induced by its neighbors and then calculates the 3-profile of this graph. A file counts_3_egos.txt is appended with input filename and runtime. Network traffic is appended to netw_counts_3_egos.txt similarly. An option (per_vertex) writes the 3-profile of each ego to file. The algorithm assumes that each undirected edge appears exactly once in the graph input. If edges may appear more than once, this procedure will over count.

	./3profileEgoSer --graph mygraph.txt --format tsv --id_list myegolist.txt --sample_iter 5


## 3profileEgoParsubegofile

Ego 3-profile Counting (parallel).

Given an undirected graph, this program computes the global 3-profile for a subset of ego subgraphs. The subset can be specified by an input file (id_list) containing vertex ids; otherwise, vertices are included with probability (vertex_egoprob). The ego 3-profiles of all selceted vertices are computed in parallel. A file counts_3_egosP.txt is appended with input filename, runtime, ego probability, and number of egos. Network traffic is appended to netw_counts_3_egosP.txt similarly. An option (per_vertex) writes the 3-profile of each ego to file. The algorithm assumes that each undirected edge appears exactly once in the graph input. If edges may appear more than once, this procedure will over count.

	./3profileEgoParsubegofile --graph mygraph.txt --format tsv --id_list myegolist.txt --sample_iter 5


## getLocalTriangles

Local Triangle Counting.

Given a graph, this program computes the total number of triangles in the graph. This is GraphLab Powergraph's standard undirected triangle count with wrappers for iteration, edge sampling, and runtime/network bandwidth statistics. A file counts_triangles.txt is appended with input file name, edge sampling probability, triangle count, and runtime. Network traffic is appended to netw_triangles.txt similarly. An option (per_vertex) is also provided which computes for each vertex, the number of triangles it is involved in. The algorithm assumes that each undirected edge appears exactly once in the graph input. If edges may appear more than once, this procedure will over count.

	./getLocalTriangles --graph mygraph.txt --format tsv --sample_iter 10 --min_prob .5 --max_prob 1 --prob_step .1

