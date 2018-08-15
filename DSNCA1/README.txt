To compile the code execute "make" via the command line. To run the code for dbs (equivalently for dsnca) execute 

./dbs <input file>


The input file must be in the following format (DIMACS):

• The first line gives the parameters of the input and has the form 

  p <N=number of vertices> <M=number of initial edges and edge updates> <ID of root vertex> <dummy vertex> 
  
The vertices have IDs in {1,2,...,N}. The dummy vertex is only required for compatibility reasons.

• The edges of the initial graph have the format: 
  
  a <ID of source vertex> <ID of target vertex>

The end of the initial graph is designated by the line

  e

• The edge insertions/deletions (might be intermixed) have the format:

  i <ID of source vertex> <ID of target vertex> (for edge insertions)

  d <ID of source vertex> <ID of target vertex> (for edge deletions)


The total number of lines starting with "a", "i" or "d" equals M. During the execution, the dominator tree is maintained in the array named "idom", where position i stores the ID of the immediate dominator of the vertex with ID i.