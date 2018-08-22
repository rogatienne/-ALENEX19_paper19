/*------------------------------------------------------------------------
 | Computes Decremental Low-High order on reducible graphs 
 | Input: A reducible graph and deletions
 *------------------------------------------------------------------------*/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
#include "rfw_timer.h"
#include <vector>
#include <stack>
#include <list>
#define MAXLINE       500   /* max length of input line */

//using namespace std;
char line[MAXLINE]; /* stores input line */

int n, n_initial, m;       // number of nodes, arcs
int r;          // root vertex

int *arcList;   // stores input arcs
int *arcList_d;
int deletions = 0;

int *edge_of_idom; // store the vertices  that have edge from their idom in the initial graph
int *in_degree ;

int *Gout;
int *GfirstOut;
int *r_Gout;
int *r_GfirstOut;

int *dom_2;

int * derived_arcs_1;
int * derived_arcs_2;

int *label2pre_Dom ; // dfs in the dominator tree
int *pre2label_Dom ;
int *parent_Dom ;

int *BRout ;
int *BRfirstOut;

 int count; // comparison counter
// increment counter
//inline void incc() {
    //count++;
//}

int *L_First;
int *L_Target;
int *L_Next;
int L_current_pos;
int *level;

int *blue; // blue spanning tree
int *red;  // red spanning tree
int *label2pre; // mapping node id -> preoder number
int *pre2label; // mapping preoder number -> node id
int *parent; // parents in the link-eval tree
int next; // next preorder number
int *semi;
int *label;
int *dom;
int *ubucket;


//for the initial graph

int current_pos ;
int r_current_pos ;
int next_free;
int r_next_free;

int *First;
int *Target;
int *Next;
int *Before;

int *r_First;
int *r_Target;
int *r_Next;
int *r_Before;


int nr; //number of vertices reachable from r
 int next_3;


/*---------------------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/
/*--------------------------------computation of the decremental LowHigh-----------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/
bool Decremental (int d_1,int d_2) {
  bool d_check ;
  d_check = false;
  int lh_check;
 // printf("\n Delete arc d(%d,%d)\n",d_1, d_2);
    //if (dom_2[d_2] == d_1)    
    //{
     
     // printf("dom_2[%d] = %d = %d ",d_2,dom_2[d_2],d_1);
     // printf("\n found\n");
     // fflush(0);
   // }
    if(dom_2[d_2] != d_1)  {
      
      int lh_order_num = label2pre_Dom[d_2];
      lh_check = 0;
       //int t;
	int j = r_First[d_2];
	while(j!=0){
		int v = r_Target[j];
		int future_next = r_Next[j];
	  
		if ((label2pre_Dom[v] < lh_order_num) && (v!=d_1))	lh_check++;

		if ((label2pre_Dom[v] > lh_order_num) && (v!=d_1)) 	lh_check++;
	  
		if (lh_check == 2) {
			d_check = true;
			break;
		}
		j = future_next;
      }
      
    }
    
  /*if (d_check == true) printf("\n There is no need for recomputing (%d,%d)\n",d_1,d_2); 
  else printf("\n Recompute Low-High Order from scratch \n");*/
  
  return d_check;
  
}


// int *derived_arcs;
int d_next;
 
void free_space() {
  
    delete [] label2pre ;
    delete [] pre2label ;
    delete [] parent ;
    delete [] dom_2 ;
    delete [] label2pre_Dom;
    delete [] edge_of_idom;
    delete [] derived_arcs_1;
    delete [] derived_arcs_2;
    delete [] red;
    delete [] blue;
  
}


/*---------------------------------------------------------------------------------------------------------------*/
/*------------------------------------ computation of the dominator tree ----------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/
inline void delete_arc_from_graph(int x,int y, int pos){
   
	if(First[x]==pos){
		First[x]=Next[pos];
		Before[Next[pos]] = 0;
	}
	else if(Next[pos]==0) {
		Next[Before[pos]] = Next[pos];
	}
	else{
		Next[Before[pos]] = Next[pos];
		Before[Next[pos]] = Before[pos];
	}
    
	if(r_First[y]==pos){
		r_First[y]=r_Next[pos];
		r_Before[r_Next[pos]] = 0;
	}
	else if(r_Next[pos]==0) {
		r_Next[r_Before[pos]] = r_Next[pos];
	}
	else{
		r_Next[r_Before[pos]] = r_Next[pos];
		r_Before[r_Next[pos]] = r_Before[pos];
	}
}

inline void rcompress(int v, int c) {
    int p;
   // incc();
    if ((p = parent[v]) > c) {
        rcompress(p, c);
       // incc();
        if (semi[label[p]] < semi[label[v]]) label[v] = label[p];
        parent[v] = parent[p];
    }
}

/* depth-first search from vertex k
   stores parents and labels        */

void DFS(int k) {
    label2pre[k] = (++next);
    pre2label[next] = k;
    //printf("pre2label[%d]=%d\n",next, k);
    
    if(k > n || k < 1){
      //printf("visited vertex %d\n",k);
    }
    int j = First[k];
    while(j!=0){      
	int v = Target[j];
	//printf("\n DFS Check edge (%d %d)\n", k, v);
	int future_next = Next[j];
       // incc();
        if (!label2pre[v]) {
            DFS(v);
            parent[label2pre[v]] = label2pre[k];
        }
        j=future_next;
    }
}

/* depth-first search from vertex k
   stores parents and labels        */
int next_2;
void DFS_INIT(int k, int *label2pre, int *pre2label) {
    label2pre[k] = ++next_2;
    pre2label[next_2] = k;
  //  printf("pre2label[%d]=%d\n",(next_2), k);
    int j = First[k];
    while(j!=0){
	int v = Target[j];
	//printf("\n DFS Check edge (%d %d) (%d,%d)\n", k, v, label2pre[k], label2pre[v]);
	int future_next = Next[j];
        
        if (!label2pre[v]) {
            DFS_INIT(v,label2pre,pre2label);
          
        }
        j=future_next;
    }
    
}


/* print tree in stdout */
void printTree(int *p, int n, char c) {
    fprintf(stdout, "\n");
    for (int i = 1; i <= n; i++) {
        fprintf(stdout, "%c %d %d\n", c, p[i], i);
    }
}
// simple Lengauer-Tarjan with Blue-Red spanning trees construction
void slt() {
    int i,j;
    label2pre = new int[n_initial + 2];
    pre2label = new int[n_initial + 2];
    parent = new int[n_initial + 2];
    
    
    for (i=0; i<=n_initial+1; i++) parent[i] = label2pre[i] = pre2label[i] = 0;
    
    
    //printf("\n slt: n=%d nr=%d\n",n,nr);
    //pre-dfs
    r = 1;
    nr = 1;
    next = count = 0;
    DFS(1);
    nr = next;
    
    
   //printf("\n slt: %d vetices are reachable from source n =%d \n", nr,n);    
//     if (nr!=n) {
// 	//printf("\n Initialize Graph for non reachable vertices \n");
// 	for (i=1; i<=nr; i++) {
// 	  if (label2pre[i] == 0){
// 	 // printf("\n Delete outcoming edges from vertex %d \n",i);
// 	    j = First[i];
// 	    while(j!=0){
// 	    int v = Target[j];
// 	    /*delete arc (i,v)*/
// 	   // printf("\n delete arc (%d,%d)\n", i,v);
// 	    
// 	    delete_arc_from_graph(i,v,j);
// 	    int future_next = Next[j];
// 	    
// 	    j=future_next;
// 	  }
// 	  
//       }
//       
//     }
//     
//    }
//    else if(nr == 1)
//    {
//      printf("\n no vertices reachable from the source \n");
//      exit(1);
//    }
   

	nr = n =  next;
  
    
  if(n == 0){
   
    if(First[1]!=0) printf("1 has outgoing edges!\n");
    exit(1);
  }
    
  semi      = new int[nr + 2];
  label     = new int[nr + 2];
  dom       = new int[nr + 2];
  ubucket   = new int[nr + 2];
  dom_2    =  new int [nr + 2];
  in_degree = new int [nr + 2];
  for (int i = 0; i <= nr + 1; i++) dom[i] = ubucket[i] = in_degree[i] =  0;
   
   
   
  // for (i=1; i<=nr; i++) printf("\n vertices are reachable from source = %d\n", pre2label[i]);
   
    // extra arrays used for B-R spanning trees construction
    
    
    bool *isred = new bool [nr + 2];
    int  *eps   = new int [nr + 2];
    red   = new int [nr + 2];
    blue  = new int [nr + 2];

    for (i=0; i<=nr + 1; i++) {
        label[i] = semi[i] = eps[i] = blue[i] = i;
        red[i] = parent[i]; isred[i] = false;
    }
    
    blue[1] = red[1] = 1;
 
   
    // process the vertices in reverse preorder as they have been visited
    for (i = nr; i > 1; i--) {
   
      // printf("\n for bucket %d\n", i);
        /*---------------------
         | process i-th bucket
         *--------------------*/
	
        for (int v = ubucket[i]; v; v = ubucket[v]) {
           // printf("processing bucket %d\n", i);
            rcompress(v, i);
            int u = label[v]; // u is a vertex with min sdom in (sdom[v],v]
          //  incc();
            dom[v] = (semi[u] < semi[v]) ? u : i;
            // u is a vertex with min sdom in (sdom[v],v]
	    eps[v] = u;
        }
        //no need to empty the bucket

        /*---------------------------------------------
         | check incoming arcs, update semi-dominators
         *--------------------------------------------*/
        int k = pre2label[i];
      //printf( "\n  processing vertex=%d, preorder=%d  nr=%d\n", k, i,nr);
        //int t;
	int j = r_First[k];
	while(j!=0){
	   
	    int v = label2pre[r_Target[j]];
	    int future_next = r_Next[j];
           // printf("\n incoming edge of %d is preorder %d, \n",k , v);
          //  incc();
            if (v) {
                int u;
             //   incc();
                if (v <= i) {
                    u = v;
                }//v is an ancestor of i
                else {
                    rcompress(v, i);
                    u = label[v];
                }
              //  incc();


                /* make B and R arc-disjoint */
                //if ( (semi[u] == semi[i]) && (blue2[i] == parent[i]) ) blue2[i] = v;

                if (semi[u] < semi[i]) {
                    semi[i] = semi[u];
                    blue[i] = v;
                }
            }
             j=future_next;
        }

        /*---------------------------
         | process candidate semidom
         *--------------------------*/
        int s = semi[i];
       // incc();
        if (s != parent[i]) { //if semidominator n not parent: add i to s's bucket
            ubucket[i] = ubucket[s];
            ubucket[s] = i;
            //printf("enter %d into bucket[%d]\n",i,s);
        } else {
            dom[i] = s; //semidominator is parent: s is a candidate dominator
        }
    }

    /*------------------
     | process bucket 1
     *-----------------*/
    for (int v = ubucket[1]; v; v = ubucket[v]) dom[v] = 1;

    /*---------------
     | recover idoms
     *--------------*/

    dom[1] = 1;
    dom_2[1] = 1;
    //idom[r] = r;
    for (i = 2; i <= nr; i++) {
       // incc();
        if (dom[i] != semi[i]) dom[i] = dom[dom[i]]; //make relative absolute
        dom_2[i] = dom[i];
	//dom_2[pre2label[i]] = pre2label[dom[i]];
        //idom[pre2label[i]] = pre2label[dom[i]];
    }

  //  for (i = 1; i <= nr; i++)  printf("\n dom [%d] = %d   \n", i, dom[i]);
   
   
 
   
   
   
    // construct blue and red spanning trees
    int dfs_parent;
    for (i = 2; i <= nr; i++) {
        dfs_parent = red[i];
        if ((!isred[eps[i]]) && (semi[eps[i]] < semi[i])) {
	//  printf("\n red [%d] = %d   \n", i, red[i]);
	 // printf("\n blue [%d] = %d   \n", i, blue[i]);
            isred[i] = true;
            int temp = red[i];
            red[i] = blue[i];
            blue[i] = temp;
        } else if ((blue[i] == dom_2[i]) || (red[i] == dom_2[i])) {
            blue[i] = red[i] = dom_2[i];
	   //  printf("\n red [%d] = %d   (red[%d] = %d)\n", i, red[i], pre2label[i], pre2label[red[i]]);
	 // printf("\n blue [%d] = %d   (blue[%d] = %d)\n", i, blue[i], pre2label[i], pre2label[blue[i]]);
        }
    }
    
  
    delete [] semi;
    delete [] label;
    delete [] ubucket;
    delete [] eps;
    delete [] isred;
    delete [] dom;


}
		
		
/*---------------------------------------------------------------------------------------------------------------*/
/*------------------------------------ computation of the derived graph ----------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/


 void push(const int level,int node){
  
 // printf("\n L_First[%d]=%d \n",level, L_First[level]);
    if(L_First[level] == 0){
       
        L_Target[L_current_pos] = node;
        L_First[level] = L_current_pos;
        L_Next[L_current_pos] = 0;
	
    }
    else{
        L_Target[L_current_pos] = node;
        L_Next[L_current_pos] = L_First[level];
        L_First[level] = L_current_pos;
    }
    L_current_pos++;
}

 int pop(int level){
    int first = L_First[level];
    int ret = L_Target[first];
    L_First[level] = L_Next[first];

    return ret;
}

 int top(int level){
    return L_Target[L_First[level]];
}

/* depth-first in dominators graph search from vertex k
   stores size and labels  */
void DomDFS(int k) {
 
  level[k] = level[dom_2[k]]+1;
  if (k>n+1 || k<0) printf("\n !! \n");
  push(level[k],k);
  
    int temp_target;
    
   for (int j = BRfirstOut[k]; j < BRfirstOut[k+1]; j++) {
	  int v = BRout[j];
	  if (dom_2[v] == k) edge_of_idom[v] = 1; // stores if there is an edge from the dominator of Gout[j]
	  temp_target = v;
	  //printf("\n %d\n",level[temp_target]);
	  if ( !level[temp_target] ) {
	      DomDFS(temp_target);
	  }   


	  if(k == dom_2[temp_target] || dom_2[k] == dom_2[temp_target]){
	    if (derived_arcs_1[temp_target] == 0) {
	      derived_arcs_1[temp_target] = k;
	       if (temp_target>n+1 || temp_target<0) printf("\n !! \n");
	    }
	    else{
	      derived_arcs_2[temp_target] = k;
	      if (temp_target>n+1 || temp_target<0) printf("\n !! \n");
	    }
	    //  printf("\n 1 Derived arc of (%d,%d) is  (%d, %d) and d_next = %d\n",k ,v,k, temp_target, d_next); 
// 	      fflush(0);
	 
	  }
	  else if(temp_target != top(level[temp_target])){
	    if (derived_arcs_1[temp_target] == 0) {
	      derived_arcs_1[temp_target] = top(level[temp_target]);
	       if (temp_target>n+1 || temp_target<0) printf("\n !! \n");
	    }
	    else{
	       derived_arcs_2[temp_target] = top(level[temp_target]);
	       if (temp_target>n+1 || temp_target<0) printf("\n !! \n");
	    }
	    //printf("\n  2 Derived arc of (%d,%d) is  (%d, %d) and d_next=%d\n",k,Gout[j],top(level[temp_target]), temp_target,d_next);
	  }
    }
    pop(level[k]);
}


void derived_graph(){


    level = new int [n + 2];

    L_First = new int [n + 2];
    L_Target = new int [m + 1];
    L_Next = new  int [n + 2];
    L_current_pos=1;

    for  (int i=0;i<=n+1;i++) level[i] = 0;
    for  (int i=0;i<=n+1;i++) L_First[i] = 0;
    d_next=0;
    
    DomDFS(1);
    
 
    
    delete [] L_First;
    delete [] L_Target;
    delete [] L_Next;

    delete [] level;
      
}



/*---------------------------------------------------------------------------------------------------------------*/
/*-----------------------------------------------Compute Low High Order------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/

/* depth-first search from vertex k
 stores parents and low high labels (label2pre)and checks just for reachability  */
void DFS_LH(int k, int *GfirstOut, int *Gout, int *label2preR, int *pre2labelR, int *parentR) {
       
	label2preR[k] = ++next_3;
	pre2labelR[next_3] = k;
	
	for (int i=GfirstOut[k];i<GfirstOut[k+1];i++){
		int j=Gout[i];
		//printf("\n check edge (%d %d)\n",k,j);
		if (!label2preR[j]) {
			DFS_LH(j,GfirstOut, Gout, label2preR, pre2labelR, parentR);
			parentR[label2preR[j]] = label2preR[k];
		}
		
	}
}

void LowHigh () {
  
    int *interval_2 = new int [n+2];
    int *parent_tree = new int [n+2];
    int *insert_x = new int [n+2];
    int *second_derived_vertex = new int [n+2];
    int *interval_1 = new int [n+2];
    
    int *GfirstOut_Dom = new int [n+4];
    int *GnextOut_Dom = new int [n+4];
    int *Gout_Dom = new int [n+4];
    
    int *label_2pre_C = new int [ n + 2];
    int *size = new int [n+2];
    int *num_of_children_parent_tree = new int [n + 2];
    
    int *Stack = new int [n + 2];
    int *Stack2 = new int [n + 2];
    int Stack2_top = 0;
   
    bool test = false;
    
    label2pre_Dom = new int [n_initial+2];
    pre2label_Dom = new int [n_initial+2];
    parent_Dom = new int [n_initial+2];
  
    
    int *arc_dom = new int [2*n+2];
     
  
    for (int i=0;i<=n+1;i++){  
      size[i] = 1;
   
      GfirstOut_Dom[i] = 0;
   
      interval_1[i] = 0;
      interval_2[i] = 0;

      label_2pre_C[i] = 0;
      num_of_children_parent_tree[i] = 0;
      parent_tree[i] = 0;
      
    }
    
  
    int Stack_top = 0, Stack_bottom = 0;
   
/*    for(int i = 1; i <= n; i++){
      if(in_degree[i] == 0) printf("vertex %d has not in edges\n",i);
    }
    for(int i = 1; i <= n; i++) in_degree[i]=0;
    printf("p %d %d\n",n,BRfirstOut[n+1]);
    for(int i = 1; i <= n; i++){
	//printf("\n\ 1 stack %d \n",i);
	for (int k = BRfirstOut[i]; k<BRfirstOut[i+1]; k++){
	  int v = BRout[k];
	  printf("a %d %d\n",i,v);
	  in_degree[v]++;
	}
    }*/
    
    /*Topological Sort in the Initial Graph*/
    int num = 1;
    
    Stack[Stack_top++] = 1;
    while (Stack_top != Stack_bottom) {
	int i = Stack[Stack_bottom++];
	//printf("\n\ 1 stack %d \n",i);
	for (int k = BRfirstOut[i]; k<BRfirstOut[i+1]; k++){
	  int v = BRout[k];
	  if(--in_degree[v] == 0) {
	    Stack[Stack_top++] = v;
	  }
	}
    }
     //printf("\n Printf stack top %d\n", Stack_top);
     delete [] BRout;
     delete [] BRfirstOut;
   
   int  d_1_c = 0;
   int  d_2_c = 0;
   
   /* Offline Execution: Process the vertices in Topological order and then construct the "Parent Tree" */
   for (int j=0; j < Stack_top;j++) {
     int i = Stack[j];     
     
     if (i!=1){
	  //printf("\n\ NUMBER 2: stack %d \n",i);
	  if (edge_of_idom[i] == 1) { /* put it anywhere in the list */
	    parent_tree[i] = dom_2[i];
	    num_of_children_parent_tree[dom_2[i]]++;
	    insert_x[i] = 1;
	    if (derived_arcs_1[i]!=dom_2[i] || derived_arcs_2[i]!=0) printf("\nwrong\n");
	     
	  }
	  else { 
	  int d_1 = derived_arcs_1[i];
	  int d_2 = derived_arcs_2[i];
	  
	    parent_tree[i] = d_1;
	    insert_x[i] = 0;
	    second_derived_vertex[i] = d_2;
	  
	    num_of_children_parent_tree[d_1]++;
	  }
     } 
    }
 
 

  
   // printf("\n Compute size of parent tree \n");
    Stack2_top = 0;
    for (int k=1; k<=n; k++){
       if(num_of_children_parent_tree[k] == 0) Stack2[Stack2_top++]=k;
    }
       
    while(Stack2_top!=0){
	  int vertex = Stack2[--Stack2_top];
	  if(--num_of_children_parent_tree[parent_tree[vertex]] ==0) Stack2[Stack2_top++] = parent_tree[vertex];
	  size[parent_tree[vertex]]  += size[vertex];

    }
    
    
    //printf("\n 1 : Printf stackt top %d\n", Stack2_top);
    
  //  if (Stack2_top>n+1 || Stack2_top<0) printf("\n !!!!1\n");
    /* for (int i=i;i<=Stack_top;i++) {
      printf("\n size[%d] = %d\n", i,size[i]);
      
     }
     */
   
     /* Initialize intervals of the root */
       interval_1[1] = 0;
       interval_2[1] = size[1];
     
    /* Online Execution: Construction of intervals and store the children of each node in a specific order */
    for (int j=0;j<Stack_top;j++) {
        int i = Stack[j];  
	if (i!=1 && i!=0){
	   // printf("\n\ stack_3 %d \n",i);
	    if (insert_x[i] == 1){ /* do simple insert(x) command */
		//printf("\n Simple Commnad for the vertex %d\n",i);
		interval_1[i] = interval_2[parent_tree[i]]- size[i] + 1;
		interval_2[i] = interval_2[parent_tree[i]];
		
		interval_2[parent_tree[i]] = interval_2[parent_tree[i]]- size[i];
		
		if(interval_1[i]<0 || interval_1[i]>n) printf("1) v:%d, p[%d]=%d, size[%d]=%d| size[%d]=%d, interval_2[%d]=%d | n=%d\n",i,i,parent_tree[i],i,size[i],parent_tree[i],size[parent_tree[i]],parent_tree[i],interval_2[parent_tree[i]],n);
		if(interval_2[parent_tree[i]]<0 || interval_2[parent_tree[i]]>n) printf("2) v:%d, p[%d]=%d, size[%d]=%d\n",i,i,parent_tree[i],i,size[i]);
		label_2pre_C[interval_1[i]] = i;
		label_2pre_C[interval_2[parent_tree[i]]] = parent_tree[i];
	       // printf("\n for vertex %d [%d,%d] parent[%d] = %d size[parent[%d]] = %d \n",i, interval_1[i],interval_2[i],i,parent_tree[i],i, size[parent_tree[i]]);
		
	    }
	      
	    else{ /*do insert(x,y,test) command*/
		if (interval_1[parent_tree[i]]<= interval_1[second_derived_vertex[i]] && interval_2[parent_tree[i]] <= interval_2[second_derived_vertex[i]] ){
		  test = true;
		  //printf("\n Insert Commnad for the vertex TRUE %d\n",i);
		}
		else {
		  test = false;
		 //  printf("\n Insert Commnad for the vertex  FALSE %d\n",i);
		}
		
		if (test == true){
		  
		  interval_1[i] = interval_2[parent_tree[i]] - size[i] + 1;
		  interval_2[i] = interval_2[parent_tree[i]] ;
		  
		  interval_2[parent_tree[i]] = interval_2[parent_tree[i]] - size[i] ;
		  
		  
		  label_2pre_C[interval_1[i]] = i;
		  label_2pre_C[interval_2[parent_tree[i]]] = parent_tree[i];
		 
		} 
		else{
		 
		  interval_1[i] = interval_1[parent_tree[i]];
		  interval_2[i] = interval_1[parent_tree[i]] + size[i] -1 ;
		 
		  
		  interval_1[parent_tree[i]] = interval_1[parent_tree[i]] + size[i];
		  
		  
		  label_2pre_C[interval_1[i]] = i;
		  label_2pre_C[interval_2[parent_tree[i]]] = parent_tree[i];
		  
		
		}
		
		// printf("\n for vertex %d [%d,%d]\n", i , interval_1[i],interval_2[i] );
	      }
	  
	  
	}
   }
   
   
    /*	Assign the number i to each item that has interval [i,i] and built dominator tree */
    int p = 0;
    arc_dom[0] = 0;
 
    
	//printf("\n Print dominator tree %d\n",Stack_top);
	//printf(" n = %d, stack_top = %d\n",n, Stack2_top);
	int k,l;
	for (int i=2;i<=n;i++){
		int k = label_2pre_C[i] ;
		int l = dom_2[label_2pre_C[i]];
     
		//  printf("\n  i = %d, label_2pre_C = %d \n",i, label_2pre_C[i] );
		if(l < 0 || k <0||l>n||k>n){
			printf("d %d %d i = %d\n",l,k,i);
			exit(1);
		}
		arc_dom[p++] = l;
		arc_dom[p++] = k;
	} 
          

     
    for (int i=0;i<=n+3;i++) GfirstOut_Dom[i] = GnextOut_Dom[i] = Gout_Dom[i] = 0;

    for (int k=0; k<p/2; k++){
        int x = arc_dom[2*k];
        int y = arc_dom[2*k+1];
		if(x+1 > n) printf("\n (%d,%d) p = %d\n", x,y,k);
        GfirstOut_Dom[x+1]++;
    }


    for (int k=1; k<=n; k++){
        GfirstOut_Dom[k] += GfirstOut_Dom[k-1];
        GnextOut_Dom[k] = GfirstOut_Dom[k];
	/////printf("\n %d %d \n",k, n);
    }
    
    for (int k=0; k<p/2; k++){
        int x = arc_dom[2*k];
        int y = arc_dom[2*k+1];
        Gout_Dom[GnextOut_Dom[x]++] = y;
	//printf("d %d %d \n",pre2label[x], pre2label[y]);
	
    }

    for (int k=0; k<=n+1; k++)label2pre_Dom[k] = 0;
    
    
    next_3= 0;
    r = 1;
    DFS_LH(r,GfirstOut_Dom, Gout_Dom, label2pre_Dom, pre2label_Dom, parent_Dom);
    
//     printf("\n n = %d nd =%d \n",n,nd);
//    printf("\n LOW-HIGH ORDER OF INPUT GRAPGH \n");
//     for (int k=1; k<=n; k++){
//      printf(" VERTEX %d HAS %d (low-high order number) \n", k, label2pre_Dom[k]);
//      printf("d %d %d \n", k, pre2label_Dom[k ]);
//        
//    }
  
    
    
    
   
   // delete [] derived_arcs_2;
   
    delete [] Stack;
    delete [] Stack2;
    delete [] GfirstOut_Dom ;
    delete [] GnextOut_Dom ;
    delete [] Gout_Dom;
    delete [] arc_dom;
    delete [] size ;
    delete [] interval_2 ;
    delete [] interval_1 ;
    delete [] parent_tree ;
    delete [] insert_x ;
    delete [] second_derived_vertex ;
    
    delete [] label_2pre_C ;
    delete [] num_of_children_parent_tree ;    
    delete [] pre2label_Dom;
    delete [] parent_Dom;

    
}
/*---------------------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/

void processInput() {

     int x,y;
 
   //printf("\n PRINT THE INITIAL GRAPH\n");
   //printf("p %d %d 1 1  \n", n,m);
   /* Compute the dominator tree and Initialize the set of the children of each vertex */
      
   
    slt();
    //printf("Domintor Tree Computed n = %d  nr = %d\n",n,nr);
    //fflush(0);
   // for (int i=0; i<=n; i++) printf("\n red %d %d\n",red[i],blue[i]);

    
    derived_arcs_1 = new int [n + 2];
    derived_arcs_2 = new int [n + 2];
    edge_of_idom = new int [n + 2];
   
    
   		
    for (int i=0; i<=n+1; i++){
        //if(i>0 && r_First[i] == 0) printf("vertex %d has no incoming edges\n",i);
	edge_of_idom[i] = 0;
	derived_arcs_1 [i] =0;
	derived_arcs_2[i] = 0; 
    } 
    
    BRout = new int [2*n + 2];
    BRfirstOut = new int [n + 2];
    int *BRnextOut  = new int[n + 2];
    
    for (int i=0; i<=(n + 1); i++) BRfirstOut[i] = BRfirstOut[i] = 0;
    for (int i=0; i<=(2*n + 1); i++)  BRout[i] = 0;

    for (int i=0; i<=n; i++) {
        BRout[2*i] = BRout[2*i+1] = BRfirstOut[i] = BRnextOut[i]  = 0 ;
        BRfirstOut[n+1] = BRnextOut[n + 1] = 0;
    }
    
    for (int i=2; i<=n; i++){
      if (blue[i] == red[i]) {
	  BRfirstOut[blue[i]+1]++; 
	// printf("\n blue[%d] = %d  red[%d] = %d found\n", i,blue[i], i ,red[i]);
      }  
      else{
	  BRfirstOut[blue[i]+1]++;
	  BRfirstOut[red[i]+1]++;
      }
    }
    for (int i=1; i<=n+1; i++) {
        BRfirstOut[i] += BRfirstOut[i-1];
        BRnextOut[i] = BRfirstOut[i];
    }
    
    
    for (int i=2; i<=n; i++) {
      if (blue[i] == red[i]) {
        BRout[BRnextOut[blue[i]]++] = i;
		in_degree[i]++;
      }
      else{
	   BRout[BRnextOut[blue[i]]++] = i;
	   BRout[BRnextOut[red[i]]++] = i;
	   in_degree[i] = in_degree[i] + 2;
      }
    }
 
 /*Compute the derived arcs of the the graph of the two divergernt spannning trees */
    derived_graph();
    

 
    delete [] BRnextOut;
    
}


/*---------------------------------------------------------------------------------------------------------------*/
/*-------------------------------------------Built Graph---------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/
inline void insert_arc_to_graph(int x,int y){
    if(First[x]==0){
        Target[current_pos]=y;
        First[x]=current_pos++;
    }
    else{
        Target[current_pos]=y;
        Next[current_pos]=First[x];
		Before[First[x]]=current_pos;
        First[x]=current_pos++;
    }
    if(r_First[y]==0){
        r_Target[r_current_pos]=x;
        r_First[y]=r_current_pos++;
    }
    else{
        r_Target[r_current_pos]=x;
        r_Next[r_current_pos]=r_First[y];
		r_Before[r_First[y]]=r_current_pos;
        r_First[y]=r_current_pos++;
    }
}



int found = 0;
void builtgraph() {
    int input_source,input_target;
    
	for (int current_input_pos = 0; current_input_pos < m; current_input_pos++) {
		input_source = arcList[2 * current_input_pos];
		input_target = arcList[2 * current_input_pos + 1];

		if (input_source > n || input_target > n) {
			printf("\n !!!!!!!!!!!!!!!! \n ");
		}
		//printf("\n insert (%d,%d)", input_source,input_target );
		insert_arc_to_graph(input_source,input_target);
		//printf("a %d %d \n",input_source,input_target);
		
     }

    delete arcList; 
   // printf("\n katy = %d m = %d\n",katy,m);
}

/*---------------------------------------------------------------------------------------------------------------*/
/*----------------------------Built the Initial Graph-------------------------------------------------------------*/
/*---------------------------------------------------------------------------------------------------------------*/
void Init_ReadGraph() {


    current_pos = r_current_pos = 1;
    
    First=new int [n + 2];
    Target=new int [m + 2];
    Next=new int [m + 2];
    Before = new int [m + 2];
    next_free = r_next_free = 1;
    
    r_First=new int [n + 2];
    r_Target=new int [m + 2];
    r_Next=new int [m + 2];
    r_Before = new int [m + 2];
    
    
    for(int i=0; i<=n+1; i++) 
    { 
      First[i] = 0;
      r_First[i] = 0;
    }
    
    for (int i=0;i<m+2;i++){
      Target[i] = 0;
      r_Target[i] = 0;
      Before[i] = 0;
      Next[i] = 0;
      r_Next[i]=0;
      r_Before[i]=0;
    }
}  

/* read graph from input file */
void readGraph(const char *file) {
    FILE *input = fopen(file, "r");
    if (!input) {
        fprintf(stderr, "Error opening file \"%s\".\n", file);
        exit(-1);
    }

    int x, y, dummy;
    int current_input_pos = 0;
    int p = 0;
    int d = 0;
    int k,l;
   

    while (fgets(line, MAXLINE, input) != NULL) {
        switch (line[0]) {
            case '\n':;
            case '\0': break;
            case 'p': if (sscanf(line, "p %d %d %d %d", &n, &m, &r, &dummy) != 4) {
                    fprintf(stderr, "Error reading graph size (%s).\n", file);
                    exit(-1);
                }
                //printf("\p %d %d 1 1 \n",n,m);
                arcList = new int[2 * m ];
		arcList_d = new int [2 * m];
		n_initial = n;
                break;
            case 'a': if (sscanf(line, "a %d %d", &x, &y) != 2) {
                    fprintf(stderr, "Error reading graph arc (%s).\n", file);
                    exit(-1);
                }
                 arcList[p++] = x;
                 arcList[p++] = y;
                break;
	  case 'e': fprintf(stderr, "read e\n");
		
		break;
			
           case 'd': if (sscanf(line, "d %d %d", &x, &y) != 2) {
                    fprintf(stderr, "Error reading graph deletion (%s).\n", file);
                    exit(-1);
                }
                
                arcList_d[d++] = x;
                arcList_d[d++] = y;
				deletions++;

                break;
            default: fprintf(stderr, "Error reading graph (%s).\n", file);
                exit(-1);
        }
    }
  //  printf("n= %d	m=%d	",n,m);
    
    m = p/2;
    fprintf(stderr, "END reading graph (%s).\n", file);
    fclose(input);
}


// process input arcs

int affected_edges = 0;
int main(int argc, char *argv[]) {
    if (argc != 2) {
        printf("\n usage: %s <input file> \n\n", argv[0]);
        exit(-1);
    }

    char *file = argv[1];
  //  int runs = atoi(argv[2]);


    r=1;
    int affected = 0;
    readGraph(file);
    
    RFWTimer timer(true);
    double t;
    
    Init_ReadGraph();
    builtgraph();
    processInput();
    LowHigh();
   
       // printf("\n we are going to make %d deletions to the initial graph\n", deletions);
    
    for (int i=0;i<deletions;i++){
		int x = arcList_d[2*i];
		int y = arcList_d[2*i + 1];  
		//if (x >n || y>n ) printf("1==========================(%d,%d) n = %d\n", x, y, n);

		//  printf("1==========================(%d,%d) n = %d\n",x,y,n);
		if (x == y) {
			printf("\n the same\n");
			continue;
		} 
		/* check if there is a need for recomputing low high order */
		if(label2pre[x] == 0 || label2pre[y] == 0) {
			affected_edges++;
			//printf("\n No need for recomputing\n");
			int j = First[x];
			while (j != 0)
			{
				int v = Target[j];
				int future_next = Next[j];
				if (v == y) delete_arc_from_graph(x, y, j);
				j = future_next;
			}
			continue;
		}
		int dec = Decremental(label2pre[x],label2pre[y]);
      
		// printf("2==========================(%d,%d)\n",x,y);

		/*Delete arc (x ,y) from the initial graph*/
		int j = First[x];
		while (j!=0)
		{
			int v = Target[j];
			int future_next=Next[j];
			if (v == y) delete_arc_from_graph(x,y,j);
			j=future_next;
		}
      
      
		//  printf("3==========================(%d,%d)\n",x,y);
		/*delete outcoming edges from vertex y*/
		int *label2pre_dec = new int [n_initial + 2];
		int *pre2label_dec = new int [n_initial + 2];
		next_2=0;
      
		for (int pi=0;pi<=n_initial;pi++) label2pre_dec[pi] = pre2label_dec[pi] = 0;;
      
		// printf("4==========================(%d,%d)\n",x,y);
		//printf("--------------\n");
		DFS_INIT(1,label2pre_dec,pre2label_dec);
       
		// printf("5==========================(%d,%d)\n",x,y);
		if(next_2 == 1){	
			if(First[1]!=0) printf("1 has outgoing edges!\n");
			else	printf("1 has no outgoing edges!\n");
			break;
		}
		if (n!=next_2) {
	
			int del=deletions;
			//printf("\n Initialize Graph for non reachable vertices reachable now =%d , reachable before =%d remaining deletions %d  \n", next_2,n,del-i);
			n = nr = next_2;
			for (int ki=1; ki<=next_2; ki++) {
				// printf("\n Delete outcoming edges from vertex %d \n",i);
				int current_vertex = pre2label_dec[ki];
				if(label2pre_dec[current_vertex]!=0) continue;
				j = First[current_vertex];
				while(j!=0){
					int v = Target[j];
					/*delete arc (i,v)*/
					//  printf("\n _delete arc (%d,%d)\n", current_vertex,v);
	      
					delete_arc_from_graph(current_vertex,v,j);
					int future_next = Next[j];
	      
					j=future_next;
				}
      
			}
        
			//printf("6==========================(%d,%d)\n",x,y);
      }
      
      //printf("\n n=%d nr=%d\n",n,nr);
      
      delete [] label2pre_dec ;
      delete [] pre2label_dec;
      
 
		if (!dec){
			affected ++;
			free_space();
	
			processInput();
			LowHigh();
		}
	}
     
     //printf("\n we should recompute for %d of %\d ", affected,deletions);
   
   
    //printf("d = %d	rec = %d	reachable =%d	",deletions,affected,next_2);
    
    t = timer.getTime();
    printf("	%f \n",t);


    return 0;
}