/*  
 * Copyright (c) 2009 Carnegie Mellon University. 
 *     All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing,
 *  software distributed under the License is distributed on an "AS
 *  IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 *  express or implied.  See the License for the specific language
 *  governing permissions and limitations under the License.
 *
 * For more about this software visit:
 *
 *      http://www.graphlab.ml.cmu.edu
 *
 */


#include <boost/unordered_set.hpp>
//#include <boost/multiprecision/cpp_int.hpp>
#include <graphlab.hpp>
#include <graphlab/ui/metrics_server.hpp>
#include <graphlab/util/hopscotch_set.hpp>
#include <graphlab/macros_def.hpp>
#include <limits>

//comment the following line if you want to use integer counters
#define  DOUBLE_COUNTERS


// This code uses Graphlab's built in hopscotch hash set. 
// It also borrows from GraphLab's built in undirected triangle count (Schank's thesis) and 3profileLocal.
// Radix sort implementation from https://github.com/gorset/radix
// Thanks to Erik Gorset


/*


Copyright 2011 Erik Gorset. All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are
permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of
conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list
of conditions and the following disclaimer in the documentation and/or other materials
provided with the distribution.

THIS SOFTWARE IS PROVIDED BY Erik Gorset ``AS IS'' AND ANY EXPRESS OR IMPLIED
WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL Erik Gorset OR
CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation are those of the
authors and should not be interpreted as representing official policies, either expressed
or implied, of Erik Gorset.
*/

//probability of keeping an edge in the edges sampling process
double sample_prob_keep = 1;
double min_prob = 1;
double max_prob = 1;
double prob_step = 0.5;
//global variables
size_t total_edges = 0;
std::vector<size_t> unique_vertex_ids; //vector or array??
int sample_iter = 1;
graphlab::vertex_id_type ego_center = 0;


void radix_sort(graphlab::vertex_id_type *array, int offset, int end, int shift) {
    int x, y;
    graphlab::vertex_id_type value, temp;
    int last[256] = { 0 }, pointer[256];

    for (x=offset; x<end; ++x) {
        ++last[(array[x] >> shift) & 0xFF];
    }

    last[0] += offset;
    pointer[0] = offset;
    for (x=1; x<256; ++x) {
        pointer[x] = last[x-1];
        last[x] += last[x-1];
    }

    for (x=0; x<256; ++x) {
        while (pointer[x] != last[x]) {
            value = array[pointer[x]];
            y = (value >> shift) & 0xFF;
            while (x != y) {
                temp = array[pointer[y]];
                array[pointer[y]++] = value;
                value = temp;
                y = (value >> shift) & 0xFF;
            }
            array[pointer[x]++] = value;
        }
    }

    if (shift > 0) {
        shift -= 8;
        for (x=0; x<256; ++x) {
            temp = x > 0 ? pointer[x] - pointer[x-1] : pointer[0] - offset;
            if (temp > 64) {
                radix_sort(array, pointer[x] - temp, pointer[x], shift);
            } else if (temp > 1) {
                std::sort(array + (pointer[x] - temp), array + pointer[x]);
                //insertion_sort(array, pointer[x] - temp, pointer[x]);
            }
        }
    }
}

size_t HASH_THRESHOLD = 64;//1000000000;

// We on each vertex, either a vector of sorted VIDs
// or a hash set (cuckoo hash) of VIDs.
// If the number of elements is greater than HASH_THRESHOLD,
// the hash set is used. Otherwise the vector is used.
struct vid_vector{
  std::vector<graphlab::vertex_id_type> vid_vec;
  graphlab::hopscotch_set<graphlab::vertex_id_type> *cset;
  vid_vector(): cset(NULL) { }
  vid_vector(const vid_vector& v):cset(NULL) {
    (*this) = v;
  }

  vid_vector& operator=(const vid_vector& v) {
    if (this == &v) return *this;
    vid_vec = v.vid_vec;
    if (v.cset != NULL) {
      // allocate the cuckoo set if the other side is using a cuckoo set
      // or clear if I alrady have one
      if (cset == NULL) {
        cset = new graphlab::hopscotch_set<graphlab::vertex_id_type>(HASH_THRESHOLD);
      }
      else {
        cset->clear();
      }
      (*cset) = *(v.cset);
    }
    else {
      // if the other side is not using a cuckoo set, lets not use a cuckoo set
      // either
      if (cset != NULL) {
        delete cset;
        cset = NULL;
      }
    }
    return *this;
  }

  ~vid_vector() {
    if (cset != NULL) delete cset;
  }

  // assigns a vector of vertex IDs to this storage.
  // this function will clear the contents of the vid_vector
  // and reconstruct it.
  // If the assigned values has length >= HASH_THRESHOLD,
  // we will allocate a cuckoo set to store it. Otherwise,
  // we just store a sorted vector
  void assign(const std::vector<graphlab::vertex_id_type>& vec) {
    clear();
    if (vec.size() >= HASH_THRESHOLD) {
        // move to cset
        cset = new graphlab::hopscotch_set<graphlab::vertex_id_type>(HASH_THRESHOLD);
        foreach (graphlab::vertex_id_type v, vec) {
          cset->insert(v);
        }
    }
    else {
      vid_vec = vec;
      if (vid_vec.size() > 64) {
        radix_sort(&(vid_vec[0]), 0, vid_vec.size(), 24);
      }
      else {
        std::sort(vid_vec.begin(), vid_vec.end());
      }
      std::vector<graphlab::vertex_id_type>::iterator new_end = std::unique(vid_vec.begin(),
                                               vid_vec.end());
      vid_vec.erase(new_end, vid_vec.end());
    }
  }

  void save(graphlab::oarchive& oarc) const {
    oarc << (cset != NULL);
    if (cset == NULL) oarc << vid_vec;
    else oarc << (*cset);
  }


  void clear() {
    vid_vec.clear();
    if (cset != NULL) {
      delete cset;
      cset = NULL;
    }
  }

  size_t size() const {
    return cset == NULL ? vid_vec.size() : cset->size();
  }

  void load(graphlab::iarchive& iarc) {
    clear();
    bool hascset;
    iarc >> hascset;
    if (!hascset) iarc >> vid_vec;
    else {
      cset = new graphlab::hopscotch_set<graphlab::vertex_id_type>(HASH_THRESHOLD);
      iarc >> (*cset);
    }
  }
};

/*
  A simple counting iterator which can be used as an insert iterator.
  but only counts the number of elements inserted. Useful for
  use with counting the size of an intersection using std::set_intersection
*/
template <typename T>
struct counting_inserter {
  size_t* i;
  counting_inserter(size_t* i):i(i) { }
  counting_inserter& operator++() {
    ++(*i);
    return *this;
  }
  void operator++(int) {
    ++(*i);
  }

  struct empty_val {
    empty_val operator=(const T&) { return empty_val(); }
  };

  empty_val operator*() {
    return empty_val();
  }

  typedef empty_val reference;
};


/*
 * Computes the size of the intersection of two vid_vector's
 */
// static uint32_t count_set_intersect(
static size_t count_set_intersect(
             const vid_vector& smaller_set,
             const vid_vector& larger_set) {

  if (smaller_set.cset == NULL && larger_set.cset == NULL) {
    size_t i = 0;
    counting_inserter<graphlab::vertex_id_type> iter(&i);
    std::set_intersection(smaller_set.vid_vec.begin(), smaller_set.vid_vec.end(),
                          larger_set.vid_vec.begin(), larger_set.vid_vec.end(),
                          iter);
    return i;
  }
  else if (smaller_set.cset == NULL && larger_set.cset != NULL) {
    size_t i = 0;
    foreach(graphlab::vertex_id_type vid, smaller_set.vid_vec) {
      i += larger_set.cset->count(vid);
    }
    return i;
  }
  else if (smaller_set.cset != NULL && larger_set.cset == NULL) {
    size_t i = 0;
    foreach(graphlab::vertex_id_type vid, larger_set.vid_vec) {
      i += smaller_set.cset->count(vid);
    }
    return i;
  }
  else {
    size_t i = 0;
    foreach(graphlab::vertex_id_type vid, *(smaller_set.cset)) {
      i += larger_set.cset->count(vid);
    }
    return i;

  }
}






/*
 * Each vertex maintains a list of all its neighbors.
 * and a final count for the number of 3-subgraphs it is involved in
 * also, whether the vertex is signaled for an ego subgraph 
 * and the number of vertices/edges when it is the ego center
 */
struct vertex_data_type {
  // A list of all its neighbors
  vid_vector vid_set;
  // The local 3-profile for this vertex
#ifdef DOUBLE_COUNTERS
  double num_triangles;
  double num_wedges;
  double num_wedges_e;
  double num_wedges_c;  
  //calculate locally in apply
  double num_disc; 
  double num_empty;
#else
  size_t num_triangles;
  size_t num_wedges;
  size_t num_wedges_e;
  size_t num_wedges_c;
  //calculate locally in apply
  size_t num_disc;
  size_t num_empty;
#endif
  bool in_ego_indicator; //use to count ego edges
  vid_vector vid_set_ORIG;
  size_t ego_edge_count;
  size_t ego_vertices;

  vertex_data_type& operator+=(const vertex_data_type& other) {
    num_triangles += other.num_triangles;
    num_wedges += other.num_wedges;
    num_wedges_e += other.num_wedges_e;
    num_wedges_c += other.num_wedges_c;
    num_disc += other.num_disc;
    num_empty += other.num_empty;
    return *this;
  }
  
  void save(graphlab::oarchive &oarc) const {
    oarc << vid_set << num_triangles << num_wedges << num_wedges_e << 
    num_wedges_c << num_disc << num_empty << in_ego_indicator << ego_edge_count << ego_vertices;
  }
  void load(graphlab::iarchive &iarc) {
    iarc >> vid_set >> num_triangles >> num_wedges >> num_wedges_e >> 
    num_wedges_c >> num_disc >>num_empty >> in_ego_indicator >> ego_edge_count >> ego_vertices;
  }
};



/*
 * Each edge counts the intersection size of its endpoints neighborhoods
 *
 */
struct edge_data_type {
  
#ifdef DOUBLE_COUNTERS
  double n3;
  double n2;
  double n2e;
  double n2c;
  //also use for ego edge count
  double n1;
#else
  size_t n3;
  size_t n2;
  size_t n2e;
  size_t n2c;
  //also use for ego edge count
  size_t n1;
#endif

  bool sample_indicator;

  void save(graphlab::oarchive &oarc) const {
    oarc << n1 << n2 << n2e << n2c << n3 << sample_indicator;
  }
  void load(graphlab::iarchive &iarc) {
    iarc >> n1 >> n2 >> n2e >> n2c >> n3 >> sample_indicator;
  }
};


/*
 * Two virtual gather depending on the iteration number mod 5
 * This is determined with the variable union_flag to union neighborhoods/accumulate subgraph counts
 */
struct set_union_sum_gather {
  graphlab::vertex_id_type v;
  std::vector<graphlab::vertex_id_type> vid_vec;

  #ifdef DOUBLE_COUNTERS
  double n3;
  double n2;
  double n2e;
  double n2c;
  double n1;
  #else
  size_t n3;
  size_t n2;
  size_t n2e;
  size_t n2c;
  size_t n1;
  #endif
  
  bool union_flag;

  set_union_sum_gather():v(-1) {
  }

  size_t size() const {
    if (union_flag) {
      if (v == (graphlab::vertex_id_type)-1) return vid_vec.size();
      else return 1;
    }
    else return 0;
  }
  
  set_union_sum_gather& operator+=(const set_union_sum_gather& other) {
    // if (context.iteration()%3 ==1) { //set union
    //split into cases with a local flag instead of a global variable
    if (union_flag) {
    
      if (size() == 0) {
        //save as tmp before overwriting, then add
        (*this) = other;
        // (*this)->v = other.v;
        return (*this); //once at end
      }
      else if (other.size() == 0) {
        return *this; //once at end
      }

      if (vid_vec.size() == 0) {
        vid_vec.push_back(v);
        v = (graphlab::vertex_id_type)(-1);
      }
      if (other.vid_vec.size() > 0) {
        size_t ct = vid_vec.size();
        vid_vec.resize(vid_vec.size() + other.vid_vec.size());
        for (size_t i = 0; i < other.vid_vec.size(); ++i) {
          vid_vec[ct + i] = other.vid_vec[i];
        }
      }
      else if (other.v != (graphlab::vertex_id_type)-1) {
        vid_vec.push_back(other.v);
      }
      return *this;

    }
    
    else {
      n3 += other.n3;
      n2 += other.n2;
      n2e += other.n2e;
      n2c += other.n2c;
      n1 += other.n1;    
      return *this;
    }

  }


void save(graphlab::oarchive& oarc) const {
    oarc << bool(vid_vec.size() == 0);
    if (vid_vec.size() == 0) oarc << v;
    else oarc << vid_vec;
    oarc << n1 << n2 << n2e << n2c << n3;
  }

  // deserialize
  void load(graphlab::iarchive& iarc) {
    bool novvec;
    v = (graphlab::vertex_id_type)(-1);
    vid_vec.clear();
    iarc >> novvec;
    if (novvec) iarc >> v;
    else iarc >> vid_vec;
    iarc >> n1 >> n2 >> n2e >> n2c >> n3;
  }

};


// To collect the set of neighbors, we need a message type which is
// basically a set of vertex IDs

bool PER_VERTEX_COUNT = false;


/*
 * This is the gathering type which accumulates an array of
 * all neighboring vertices.
 * It is a simple wrapper around a vector with
 * an operator+= which simply performs a  +=
 */
struct set_union_gather {
  graphlab::vertex_id_type v;
  std::vector<graphlab::vertex_id_type> vid_vec;

  set_union_gather():v(-1) {
  }

  size_t size() const {
    if (v == (graphlab::vertex_id_type)-1) return vid_vec.size();
    else return 1;
  }
  /*
   * Combining with another collection of vertices.
   * Union it into the current set.
   */
  set_union_gather& operator+=(const set_union_gather& other) {
    if (size() == 0) {
      (*this) = other;
      return (*this);
    }
    else if (other.size() == 0) {
      return *this;
    }

    if (vid_vec.size() == 0) {
      vid_vec.push_back(v);
      v = (graphlab::vertex_id_type)(-1);
    }
    if (other.vid_vec.size() > 0) {
      size_t ct = vid_vec.size();
      vid_vec.resize(vid_vec.size() + other.vid_vec.size());
      for (size_t i = 0; i < other.vid_vec.size(); ++i) {
        vid_vec[ct + i] = other.vid_vec[i];
      }
    }
    else if (other.v != (graphlab::vertex_id_type)-1) {
      vid_vec.push_back(other.v);
    }
    return *this;
  }
  
  // serialize
  void save(graphlab::oarchive& oarc) const {
    oarc << bool(vid_vec.size() == 0);
    if (vid_vec.size() == 0) oarc << v;
    else oarc << vid_vec;
  }

  // deserialize
  void load(graphlab::iarchive& iarc) {
    bool novvec;
    v = (graphlab::vertex_id_type)(-1);
    vid_vec.clear();
    iarc >> novvec;
    if (novvec) iarc >> v;
    else iarc >> vid_vec;
  }
};

/*
 * Define the type of the graph
 */
typedef graphlab::distributed_graph<vertex_data_type,
                                    edge_data_type> graph_type;


//move init outside constructor (must be declared after graph_type)
void init_vertex(graph_type::vertex_type& vertex) { 
  vertex.data().num_triangles = 0; 
  vertex.data().num_wedges = 0;
  vertex.data().num_wedges_e = 0;
  vertex.data().num_wedges_c = 0; 
  vertex.data().num_disc = 0; 
  vertex.data().num_empty = 0;
}


void sample_edge(graph_type::edge_type& edge) {
  //something based on degree here????
  if(graphlab::random::rand01() < sample_prob_keep)   
    edge.data().sample_indicator = 1;
  else
    edge.data().sample_indicator = 0;
}


class get_full_neighborhoods : //always full
      public graphlab::ivertex_program<graph_type,
                                      set_union_gather>,
      /* I have no data. Just force it to POD */
      public graphlab::IS_POD_TYPE  {
public:

  // Gather on all edges
  edge_dir_type gather_edges(icontext_type& context,
                             const vertex_type& vertex) const {
    return graphlab::ALL_EDGES;
  } 

  /*
   * For each edge, figure out the ID of the "other" vertex
   * and accumulate a set of the neighborhood vertex IDs.
   */
  gather_type gather(icontext_type& context,
                     const vertex_type& vertex,
                     edge_type& edge) const {
    set_union_gather gather;
    // if(edge.data().sample_indicator == 0){ //bug, uncomment this??
      // gather.v = -1; 
    // }
    // else{
      graphlab::vertex_id_type otherid = edge.target().id() == vertex.id() ?
                                       edge.source().id() : edge.target().id();

      gather.v = otherid; 
    // } 
   return gather;
  }

  /*
   * the gather result now contains the vertex IDs in the neighborhood.
   * store it on the vertex. 
   */
  void apply(icontext_type& context, vertex_type& vertex,
             const gather_type& neighborhood) {
   if (neighborhood.vid_vec.size() == 0) {
     // neighborhood set may be empty or has only 1 element
     vertex.data().vid_set_ORIG.clear();
     if (neighborhood.v != (graphlab::vertex_id_type(-1))) {
       vertex.data().vid_set_ORIG.vid_vec.push_back(neighborhood.v);
     }
   }
   else {
     vertex.data().vid_set_ORIG.assign(neighborhood.vid_vec);
   }
  } // end of apply

  /*no scatter*/
  edge_dir_type scatter_edges(icontext_type& context,
                              const vertex_type& vertex) const {
    return graphlab::NO_EDGES;
  }

};



/*
 * This class implements the ego 3-profile (global 3-profile for the ego subgraph) as described in
 * the header. On gather, we accumulate a set of all adjacent vertices.
 * This performs one of 5 virtual engines based on the 
 * iteration number context.iteration() modulo 5
 */

class iterated_ego_count :
      public graphlab::ivertex_program<graph_type,
                                      set_union_sum_gather>,
      /* I have no data. Just force it to POD */
      public graphlab::IS_POD_TYPE  {
public:
  bool do_not_scatter;

  // Gather on all edges
  edge_dir_type gather_edges(icontext_type& context,
                             const vertex_type& vertex) const {
    //sample edges here eventually, maybe by random edge.id() so consistent between the 2 engines?
    return graphlab::ALL_EDGES;
  } 

  /*
   * For each edge, figure out the ID of the "other" vertex
   * and accumulate a set of the neighborhood vertex IDs.
   */
  gather_type gather(icontext_type& context,
                     const vertex_type& vertex,
                     edge_type& edge) const {
    //std::cout << "Entering gather...: \n";
    set_union_sum_gather gather;
    // std::cout << "Iteration: " << context.iteration() << ", ego 3 profile G "<< vertex.id() 
    //get neighbor lists for this ego
    if (context.iteration()%5 ==1) {
      gather.union_flag = 1; //set_union
      if((edge.data().sample_indicator == 0) || (edge.source().data().in_ego_indicator == 0) || (edge.target().data().in_ego_indicator == 0)) {
        gather.v = -1; 
      }
      else{
        graphlab::vertex_id_type otherid = edge.target().id() == vertex.id() ?
                                         edge.source().id() : edge.target().id();
        gather.v = otherid; //will this work? what is v??
     } 
     // ego_edges += 1; //get the total number of edges in this ego??
     gather.n1 = 0;
     gather.n2 = 0;
     gather.n2e = 0;
     gather.n2c = 0;
     gather.n3 = 0;
     return gather;
    }
    
    //count ego_edge
    else if (context.iteration()%5 ==2) { 
      gather.union_flag = 0; //edge sum
      if (edge.target().id() == vertex.id()) {
        gather.n1 = edge.source().data().vid_set.size();
      }
      else {
        gather.n1 = edge.target().data().vid_set.size();
      }
      
      gather.n2 = 0;
      gather.n2e = 0;
      gather.n2c = 0;
      gather.n3 = 0;
      gather.v = -1; 
      return gather;
    }

    //edge pivot for local 3-profiles
    else if (context.iteration()%5 ==3) { 
      gather.union_flag = 0; //edge sum
      if( (edge.data().sample_indicator == 1) && (edge.source().data().in_ego_indicator == 1) && (edge.target().data().in_ego_indicator == 1)) {
        gather.n1 = edge.data().n1;
        gather.n2 = edge.data().n2;
        gather.n3 = edge.data().n3;
        if (vertex.id() == edge.source().id()){
          gather.n2e = edge.data().n2e;
          gather.n2c = edge.data().n2c;
        }
        else{
          gather.n2e = edge.data().n2c;
          gather.n2c = edge.data().n2e;
        }
      }
      else{
        gather.n1 = 0;
        gather.n2 = 0;
        gather.n2e = 0;
        gather.n2c = 0;
        gather.n3 = 0;
      }
      gather.v = -1; 
      return gather;
    }

    //reduce on the ego vertex to get global count (reuse the n's)
    else if (context.iteration()%5 == 4) {
      gather.union_flag = 0; //edge sum      
      if (vertex.id() == edge.target().id()) {
        gather.n3 = edge.source().data().num_triangles;
        gather.n2 = edge.source().data().num_wedges;
        gather.n2e = edge.source().data().num_disc;
        gather.n1 = edge.source().data().num_empty;
      }
      else {
        gather.n3 = edge.target().data().num_triangles;
        gather.n2 = edge.target().data().num_wedges;
        gather.n2e = edge.target().data().num_disc;
        gather.n1 = edge.target().data().num_empty;
      }

      gather.v = -1;
      gather.n2c = 0;
      return gather; //necessary?
    }
    else {
      gather.union_flag = 0;
      gather.n1 = 0;
      gather.n2 = 0;
      gather.n2e = 0;
      gather.n2c = 0;
      gather.n3 = 0;
      gather.v = -1;
      return gather;
    }
  }

  /*
   * store the gather results (neighborhood, count) on the vertex
   */
  void apply(icontext_type& context, vertex_type& vertex,
             const gather_type& neighborhood_ecounts) {
   // std::cout << "Iteration: " << context.iteration() << ", ego 3 profile A "<< vertex.id() << std::endl; 
   //neighborhood set
   if (context.iteration()%5 ==1) {
     do_not_scatter = false;
     if (neighborhood_ecounts.vid_vec.size() == 0) {
       // neighborhood set may be empty or has only 1 element
       vertex.data().vid_set.clear();
       if (neighborhood_ecounts.v != (graphlab::vertex_id_type(-1))) {
         vertex.data().vid_set.vid_vec.push_back(neighborhood_ecounts.v);
       }
     }
     else {
       vertex.data().vid_set.assign(neighborhood_ecounts.vid_vec);
     }
     do_not_scatter = vertex.data().vid_set.size() == 0;
    
    size_t tosig = context.iteration()/5;  
    if (tosig < (size_t)unique_vertex_ids.size()) //is this check necessary?
      context.signal_vid( (graphlab::vertex_id_type)unique_vertex_ids[tosig] ); //signal to get ego_edges
   }
   
   //ego_edges are double counted
   else if (context.iteration()%5 ==2) {
    vertex.data().ego_edge_count = neighborhood_ecounts.n1/2; //double counted!
   }

   //per vertex counts, signal the current ego vertex
   else if (context.iteration()%5 ==3) {
    vertex.data().num_triangles = neighborhood_ecounts.n3 / 2;
    //vertex.data().num_wedges = ecounts.n2 - ( pow(vertex.data().vid_set.size(),2) + 3*vertex.data().vid_set.size() )/2 +
      //  vertex.data().num_triangles;

    // std::cout << "Ego edges: " << vertex.data().ego_edge_count << std::endl;
    // std::cout << "Ego vertices: " << ego_vertices << std::endl;
    // std::cout << "neighborhood size: " << vertex.data().vid_set.size() << std::endl;

    vertex.data().num_wedges_c = neighborhood_ecounts.n2c/2;
    vertex.data().num_wedges_e = neighborhood_ecounts.n2e;
    vertex.data().num_wedges = vertex.data().num_wedges_e + vertex.data().num_wedges_c;
    vertex.data().num_disc = neighborhood_ecounts.n1 + vertex.data().ego_edge_count - vertex.data().vid_set.size() - vertex.data().num_triangles - vertex.data().num_wedges_e;
    vertex.data().num_empty = (vertex.data().ego_vertices  - 1)*(vertex.data().ego_vertices - 2)/2 -
        (vertex.data().num_triangles + vertex.data().num_wedges + vertex.data().num_disc);
    vertex.data().vid_set.clear(); //still necessary when iterating the engine, ORIG not cleared but this should be cleared
    //print the answers, and save to a log file at the command line?
    //signal the ego center vertex for reduction
    // std::cout << "Reducing on vertex: " << context.iteration()/5 << std::endl;
    context.signal_vid( (graphlab::vertex_id_type) unique_vertex_ids[context.iteration()/5] );    
   }

   //get final count, signal the next ego id in the list
   else if (context.iteration()%5 ==4) {
    //get a final count, signal the next id
    //store (too much space...) or just print??
    if (PER_VERTEX_COUNT) {
      //not exactly right to apply estimators to vertex counts instead of global, 
      //accuracy not well defined, this probably only works on high degree vertices
      std::cout << 
      // // "Iteration: " << context.iteration() << ", ego 3 profile "<< 
      vertex.id() << "\t" 
      << round((neighborhood_ecounts.n3/3)/pow(sample_prob_keep, 3)) << "\t" 
      << round((neighborhood_ecounts.n2/3)/pow(sample_prob_keep, 2) - (1-sample_prob_keep)*(neighborhood_ecounts.n3/3)/pow(sample_prob_keep, 2)) << "\t"
      << round((neighborhood_ecounts.n2e/3)/sample_prob_keep - (1-sample_prob_keep)*(neighborhood_ecounts.n2/3)/pow(sample_prob_keep, 2))<< "\t" 
      << round((neighborhood_ecounts.n1/3) - (1-sample_prob_keep)*(neighborhood_ecounts.n2e/3)/sample_prob_keep) << std::endl;
    }
    
    size_t tosig = context.iteration()/5 + 1;  
    if (tosig < (size_t)unique_vertex_ids.size()) {
      //std::cout << "Iteration: " << context.iteration()
      //<< " finished, now signaling vertex id: " << unique_vertex_ids[tosig] << std::endl;
      context.signal_vid( (graphlab::vertex_id_type)unique_vertex_ids[tosig] );
      //std::cout << "signaled OK " << std::endl;
    }

   }

 }


  /*
   * Scatter over all edges to compute the intersection.
   * I only need to touch each edge once, so if I scatter just on the
   * out edges, that is sufficient.
   */
  edge_dir_type scatter_edges(icontext_type& context,
                              const vertex_type& vertex) const {
    // if (context.iteration()%5 ==0 || context.iteration()%5 ==2) {
    if (context.iteration()%5 ==0 || context.iteration()%5 ==2 || context.iteration()%5==3) {
      return graphlab::ALL_EDGES;
    } 
    else if ((context.iteration()%5 ==1 && do_not_scatter) || (context.iteration()%5==4))
        return graphlab::NO_EDGES;
      // else if (context.iteration()%5==4) {
        // std::cout << "signaled." << std::endl;
        // return graphlab::NO_EDGES;
    // }
    else return graphlab::OUT_EDGES;
  }


  /*
   * Send neighborhoods to other vertex
   * For each edge, count the intersections required for local 3-profiles
   * Setup neighbors to be in the ego, or pass the ego_edge_count to neighbors
   */
  void scatter(icontext_type& context,
              const vertex_type& vertex,
              edge_type& edge) const {
    // std::cout << "Iteration: " << context.iteration() << ", ego 3 profile S "<< vertex.id() << std::endl; 
    //local 3-profile
    if (context.iteration()%5 ==1) {
      //    vertex_type othervtx = edge.target();
      if((edge.data().sample_indicator == 1) && (edge.source().data().in_ego_indicator == 1) && (edge.target().data().in_ego_indicator == 1)) {
        const vertex_data_type& srclist = edge.source().data();
        const vertex_data_type& targetlist = edge.target().data();
        size_t tmp= 0, tmp2 = 0;
        if (targetlist.vid_set.size() < srclist.vid_set.size()) {
          tmp = count_set_intersect(targetlist.vid_set, srclist.vid_set);
        }
        else {
          tmp = count_set_intersect(srclist.vid_set, targetlist.vid_set);
        }
        tmp2 = srclist.vid_set.size() + targetlist.vid_set.size(); //not needed anymore?
        edge.data().n3 = tmp;
        edge.data().n2 =  tmp2 - 2*tmp; //not needed anymore?
        
        edge.data().n2c = srclist.vid_set.size() - tmp - 1;
        edge.data().n2e = targetlist.vid_set.size() - tmp - 1;       
        // edge.data().n1 = context.num_vertices() - (tmp2 - tmp);
        edge.data().n1 = edge.target().data().ego_vertices - (tmp2 - tmp);
      }
    }

    //scatter ego_edge_count to neighbors for to neighbors for counts
    else if (context.iteration()%5 ==2) { 
      if (vertex.id() == edge.target().id()) {
        context.signal(edge.source());
        edge.source().data().ego_edge_count = vertex.data().ego_edge_count;
      }
      else if (vertex.id() == edge.source().id()) {
        context.signal(edge.target());
        edge.target().data().ego_edge_count = vertex.data().ego_edge_count;
      }
    }

    //reset ego indicator when the neighbors are done, right before passing to ego center 
    //for some reason, scatter on all edges instead of just out edges......
    else if (context.iteration()%5 ==3) {
        edge.source().data().in_ego_indicator = 0;
        edge.target().data().in_ego_indicator = 0;
    }
    
    //signal neighbors for next round, set indicator flag and scatter the number of vertices for counts
    else if (context.iteration()%5 == 0){
      // std::cout << "Iteration: " << context.iteration() << " signaling neighbors" << std::endl;
      if (vertex.id() == edge.target().id()) {
        context.signal(edge.source());
        edge.source().data().in_ego_indicator = 1; //where is this cleared?
        edge.source().data().ego_vertices = vertex.data().vid_set_ORIG.size();
        // if (vertex.id()==1) std::cout << "1s nbh " << edge.source().id() << std::endl;
      }
      else if (vertex.id() == edge.source().id()) {
        context.signal(edge.target());
        edge.target().data().in_ego_indicator = 1;
        edge.target().data().ego_vertices = vertex.data().vid_set_ORIG.size();
        // if (vertex.id()==1) std::cout << "1s nbh " << edge.target().id() << std::endl;
      }
    }
  
  }
  
};



//typedef graphlab::synchronous_engine<triangle_count> engine_type;

/* Used to sum over all the edges in the graph in a
 * map_reduce_edges call
 * to get the total number of triangles
 */
// size_t get_edge_data(const graph_type::edge_type& e) {
//   return e.data();
// }

vertex_data_type get_vertex_data(const graph_type::vertex_type& v) {
  return v.data();
}

//For sanity check of total edges via total degree
//size_t get_vertex_degree(const graph_type::vertex_type& v){
//	return v.data().vid_set.size();
//}

size_t get_edge_sample_indicator(const graph_type::edge_type& e){
        return e.data().sample_indicator;
}


size_t get_vertex_ego_indicator(const graph_type::vertex_type& v){
        return v.data().in_ego_indicator;
}

/*ego vertex signaling functions*/
/*void ego_vertex(graph_type::vertex_type& vertex) {
  //keep if ego center is a neighbor
  if ((std::binary_search(vertex.data().vid_set_ORIG.vid_vec.begin(), vertex.data().vid_set_ORIG.vid_vec.end(), ego_center)) ){
    vertex.data().in_ego_indicator = 1;
    // std::cout<<"Ego vertex "<<ego_center<< ": vertex indicator to "<<vertex.id()<<std::endl;
  }
  else
    vertex.data().in_ego_indicator = 0;
}*/



/*
 * A saver which saves a file where each line is a vid / # triangles pair
 */
struct save_profile_count{
  std::string save_vertex(graph_type::vertex_type v) { 
  //   double nt = v.data().num_triangles;
  //   double n_followed = v.num_out_edges();
  //   double n_following = v.num_in_edges();

  //   return graphlab::tostr(v.id()) + "\t" +
  //          graphlab::tostr(nt) + "\t" +
  //          graphlab::tostr(n_followed) + "\t" + 
  //          graphlab::tostr(n_following) + "\n";
  //
  /* WE SHOULD SCALE THE LOCAL COUNTS WITH p_sample BEFORE WRITING TO FILE!!!*/
  return graphlab::tostr(v.id()) + "\t" +
         graphlab::tostr(v.data().num_triangles) + "\t" +
         graphlab::tostr(v.data().num_wedges) + "\t" +
         graphlab::tostr(v.data().num_disc) + "\t" +
         graphlab::tostr(v.data().num_empty) + "\n";
  }
  std::string save_edge(graph_type::edge_type e) {
    return "";
  }
};


int main(int argc, char** argv) {

  graphlab::command_line_options clopts("Ego 3-profile Counting (serial). "
    "Given an undirected graph, this program computes the global 3-profile for a "
    "specified list of ego subgraphs (id_list). For vertex id in the input list, "
    "the serial algorithm computes the ego subgraph induced by its neighbors and then"
    "calculates the 3-profile of this graph. "
    "A file counts_3_egos.txt is appended with input filename and runtime. "
    "Network traffic is appended to netw_counts_3_egos.txt similarly. "
    "A flag (per_vertex) controls printing the 3-profile of each ego to standard output. "
    "The algorithm assumes that each undirected edge appears exactly once "
    "in the graph input. If edges may appear more than once, this procedure "
    "will over count. ");
  std::string prefix, format;
  std::string per_vertex;
  std::string vertex_id_filename;
  clopts.attach_option("graph", prefix,
                       "Graph input. reads all graphs matching prefix*");
  clopts.attach_option("format", format,
                       "The graph format");
  clopts.attach_option("id_list", vertex_id_filename,
                       "Vertex ID list. calculate egos on all vertices in this file");
  clopts.attach_option("ht", HASH_THRESHOLD,
                       "Above this size, hash sets are used (hardcoded very large)");
  clopts.attach_option("per_vertex", per_vertex,
                       "If not empty, will count the number of "
                       "triangles each vertex belongs to and "
                       "save to file with prefix \"[per_vertex]\". ");
  clopts.attach_option("sample_iter", sample_iter,
                       "Number of sampling iterations (no per vertex count)");
  //are these fully supported?
  clopts.attach_option("sample_keep_prob", sample_prob_keep,
                       "Probability of keeping edge during sampling");
  clopts.attach_option("min_prob", min_prob,
                         "min prob");
  clopts.attach_option("max_prob", max_prob,
                         "max prob");
  clopts.attach_option("prob_step", prob_step,
                         "prob step");

  if(!clopts.parse(argc, argv)) return EXIT_FAILURE;
  if (prefix == "") {
    std::cout << "--graph is not optional\n";
    clopts.print_description();
    return EXIT_FAILURE;
  }
  else if (format == "") {
    std::cout << "--format is not optional\n";
    clopts.print_description();
    return EXIT_FAILURE;
  }
  else if (vertex_id_filename == "") {
    std::cout << "--id_list is not optional\n";
    clopts.print_description();
    return EXIT_FAILURE;
  }

  if ((per_vertex != "") & (sample_iter > 1)) {
    std::cout << "--multiple iterations for no writing only\n";
    clopts.print_description();
    return EXIT_FAILURE;
  }

  if (per_vertex != "") PER_VERTEX_COUNT = true;
  // Initialize control plane using mpi
  graphlab::mpi_tools::init(argc, argv);
  graphlab::distributed_control dc;

  //graphlab::launch_metric_server();
  // load graph
  graph_type graph(dc, clopts);
  graph.load_format(prefix, format);
  graph.finalize();
  dc.cout() << "Number of vertices: " << graph.num_vertices() << std::endl
            << "Number of edges (before sampling):    " << graph.num_edges() << std::endl;

  dc.cout() << "sample_prob_keep = " << sample_prob_keep << std::endl;
  dc.cout() << "sample_iter = " << sample_iter << std::endl;



  // read global IDs in to the vector "global_vid_vec"
  std::ifstream IDstream;
  // char lname[50];
  // sprintf(lname,vertex_id_filename);
  // IDstream.open(lname);
  IDstream.open(vertex_id_filename.c_str(),std::ifstream::in); //is this ok?
  // for (size_t id; IDstream >> id;) { //c++11 only
  //   unique_vertex_ids.push_back(id);
  // }
  //getline instead?
  size_t id;
  std::string linestring;
  while (getline(IDstream,linestring)) {
    std::istringstream li(linestring);  
    li >> id;
    unique_vertex_ids.push_back(id);
  }
  IDstream.close();
  //dc.cout() << "unique id 1 is " << unique_vertex_ids[0] << ", unique id 5 is " << unique_vertex_ids[4] << std::endl;


  size_t reference_bytes;
  double total_time;

  if(min_prob == max_prob){//i.e., they were not specified by user
    min_prob = sample_prob_keep;
    max_prob = sample_prob_keep;
  }

  //read array of vertex ids, either all or subset to compare with ego2

  double new_sample_prob = min_prob;
  while(new_sample_prob <= max_prob+0.00000000001){
    sample_prob_keep = new_sample_prob;
    new_sample_prob += prob_step;  
  //START ITERATIONS HERE
  for (int sit = 0; sit < sample_iter; sit++) {
  
    reference_bytes = dc.network_bytes_sent();

    dc.cout() << "Iteration " << sit+1 << " of " << sample_iter << ". current sample prob: " << sample_prob_keep <<std::endl;


    // size_t num_h10 = 0; //total cliques in the graph (for debugging)
    // size_t num_h9 = 0; //total diamonds in the graph (for debugging)
    // size_t num_h8 = 0; //total paws in the graph (for debugging)
    // size_t num_h6 = 0; //total claws in the graph (for debugging)

    graphlab::timer ti;
    
    // Initialize the vertex data
    graph.transform_vertices(init_vertex);

    //Sampling
    graph.transform_edges(sample_edge);
    //total_edges = graph.map_reduce_vertices<size_t>(get_vertex_degree)/2;
    total_edges = graph.map_reduce_edges<size_t>(get_edge_sample_indicator);
    dc.cout() << "Total edges counted (after sampling):" << total_edges << std::endl;


    //engine just for neighborhoods that dont change with ego sampling?
    graphlab::synchronous_engine<get_full_neighborhoods> engine0(dc, graph, clopts);
    engine0.signal_all();
    engine0.start();


    // create engine to count the number of triangles
    dc.cout() << "Counting Ego subgraphs..." << std::endl;
    

    //NEW CODE
    graphlab::synchronous_engine<iterated_ego_count> engine12it(dc, graph, clopts);
    //engine12it.signal(0);
    engine12it.signal( (graphlab::vertex_id_type) unique_vertex_ids[0] ); 
    //dc.cout() << "first signal OK" << std::endl;
    //dc.cout() << "starting engine without signal" << std::endl;
    // GASphase = 2; //signal the neighbors of vertex with id 0
    //engine0.signal_all();    
    engine12it.start();
    
  

    total_time = ti.current_time();
    dc.cout() << "Total runtime: " << total_time << "sec." << std::endl;

    // //global counts not stored anywhere except printed
    // vertex_data_type global_counts = graph.map_reduce_vertices<vertex_data_type>(get_vertex_data);
    // num_h10 = global_counts.num_triangles/4;
    // num_h9 = global_counts.num_wedges/2;
    // num_h8 = global_counts.num_disc;
    // num_h6 = global_counts.num_empty;
    // dc.cout() << "Number of ego triangles (N10): " << num_h10 << std::endl; 
    // dc.cout() << "Number of ego wedge (N9): " << num_h9 << std::endl; 
    // dc.cout() << "Number of ego disc (N8): " << num_h8 << std::endl; 
    // dc.cout() << "Number of ego empty (N6): " << num_h6 << std::endl; 
   
    std::ofstream myfile;
    char fname[20];
    sprintf(fname,"counts_3_egos.txt");
    bool is_new_file = true;
    if (std::ifstream(fname)){
      is_new_file = false;
    }
    myfile.open (fname,std::fstream::in | std::fstream::out | std::fstream::app);
    if(is_new_file) myfile << "#graph\tidfile\truntime" << std::endl;
    myfile << prefix << "\t"
    << vertex_id_filename << "\t"
    //<< sample_prob_keep << "\t"
           << std::setprecision (6)
           << total_time
           << std::endl;

    myfile.close();

    sprintf(fname,"netw_3_egos_%d.txt",dc.procid());
    myfile.open (fname,std::fstream::in | std::fstream::out | std::fstream::app);

    myfile << dc.network_bytes_sent() - reference_bytes <<"\n";

    myfile.close();

    
    
    // else {
    //   graph.save(per_vertex,
    //           save_profile_count(),
    //           false, /* no compression */
    //           true, /* save vertex */
    //           false, /* do not save edge */
    //           1); /* one file per machine */
    //           // clopts.get_ncpus());

    // }
    

  }//for iterations
  }//while min/max_prob

  //graphlab::stop_metric_server();

  graphlab::mpi_tools::finalize();

  return EXIT_SUCCESS;
} // End of main

