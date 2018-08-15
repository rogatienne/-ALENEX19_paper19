/*---------------------------------------------------------------
 | Dynamic Dominators - Depth Based Search algorithm
 | uses SNCA for batch processing
 *---------------------------------------------------------------*/

#include <stdio.h>
#include <stdlib.h>
#include "rfw_timer.h"
#include <assert.h>

using namespace std;

#define MAXLINE       100   /* max length of input line */
#define INPUT_a 0
#define INPUT_i 1
#define INPUT_d 2
#define INPUT_e 3

char line[MAXLINE]; /* stores input line */

void printGraph(int * first_arr,int * target_arr,int *next_arr);

int *input_file; // stores input arcs

int r; // source
int n, m; /* number of nodes, arcs */


int *buffer;

int *First;
int *Target;
int *Next;
int *r_First;
int *r_Target;
int *r_Next;
int current_pos;
int r_current_pos;

int nca; // nearest common ancestor of updated edge endpoints
int ccount; // comparison counter
int cvertices; // number of vertices processed
int cedges; // number of arcs processed

int *label2pre; // mapping node id -> preoder number
int *pre2label; // mapping preoder number -> node id
int *parent; // parents in the link-eval tree
int *semi;
int *label;
int *dom;
int *spath; // predecessors from sdom-paths
int *dfsparent; // parents in DFS tree

// increment coounters
inline void incc() { } //ccount++; }
inline void incv() { } //cvertices++; }
inline void ince() { } //cedges++; }


/******************* BUCKET STRUCTURE *********************/
// stores affected vertices by level
int *bucket_first;
int *bucket_target;
int *bucket_next;
int bucket_last_pos;

int bucketlevel; // max level of a vertex in bucket
int *level; // level array

// insert vertex v into bucket[level[v]]
inline void insertbucket(int v) {
    int level_of_v=level[v];

    bucket_target[bucket_last_pos]=v;

    if(bucket_first[level_of_v]==0){
        bucket_first[level_of_v]=bucket_last_pos;
    }
    else{
        bucket_next[bucket_last_pos]=bucket_first[level_of_v];
        bucket_first[level_of_v]=bucket_last_pos;
    }
    bucket_last_pos++;
}

// extract a vertex from bucket of maximum level
inline int getbucket() {
    int v;
    while ( (bucket_first[bucketlevel]==0) && (bucketlevel>0) ) bucketlevel--;
    if (bucketlevel==0) return 0;
    int p = bucket_first[bucketlevel]; // possition of next node
    // v = bucket_target[bucket_first[bucketlevel]];
    v = bucket_target[p];
    //bucket_first[bucketlevel]=bucket_next[bucket_first[bucketlevel]];
    bucket_first[bucketlevel] = bucket_next[p];
    bucket_next[p] = 0;
    return v;
}


/******************* BUCKET STRUCTURE *********************/

int *idom; // dominator tree
bool *visited; // true for visited vertices
bool *affected; // true for affected (or possibly affected by deletion) vertices

int *affectedQueue; // stores (possibly) affected vertices
int first_affectedQueue;
int last_affectedQueue;

int *arcQueue; // stores (possibly) affected vertices
int first_arcQueue;
int last_arcQueue;

int *levelQueue; // stores (vertex,level) pairs for vertices that change level
int first_levelQueue;
int last_levelQueue;

//queue<int> arcQueue; // stores arcs to be processed
//queue<int> levelQueue; // stores (vertex,level) pairs for vertices that change level

// compute nearest common ancestor
inline int intersectLevel(int v1, int v2)
{
    //printf("begin intersectLevel %d %d\n",v1,v2);
    int x=v1;
    int y=v2;
    if (v1==0) return y;
    if (v2==0) return x;
    while (v1 != v2){
        incc();
        if (level[v1] >= level[v2]) {incc(); v1 = idom[v1];}
        if (level[v2] >  level[v1]) {incc(); v2 = idom[v2];}
    }
    //printf("end intersectLevel\n");
    return v1;
}

// checks if levels are updated correctly -- used for debugging
void checkLevels() {

    for (int k=1; k<=n; k++) {
        if (k==r) assert(level[k]==1);
        else {
            if ( (idom[k]) && (level[k]!=(level[idom[k]]+1)) ) {
                fprintf(stdout,"LEVEL ERROR\n");
                fprintf(stdout,"idom[%d]=%d, level[%d]=%d,level[%d]=%d",k,idom[k],k,level[k],idom[k],level[idom[k]]); exit(-1);
                exit(-1);
            }
        }
    }
}

// checks that for all arcs (u,v), either nca(u,v)=idom(v) or nca(u,v)=v -- used for debugging
void checkNCA() {
    int i,nca;
	int j;
    for (i = 1; i <= n; i++) {
        if (!idom[i]) continue;

        j=First[i];
        while(j!=0){
            int k = Target[j];
            if (!idom[k]){
                j=Next[j];
                continue;
            }
            nca = intersectLevel(i,k);
            if ( (nca!=idom[k]) && (nca!=k) )
            {
                fprintf(stdout,"ERROR NCA TEST\n");
                fprintf(stdout,"node %d, arc from %d, nca %d, idom %d, level[nca] %d, level[idom] %d \n",k,i,nca,idom[k],level[nca],level[idom[k]]);
                exit(-1);
            }
            j=Next[j];
        }
    }
}


// initialization
void init(int N,int M) {
    current_pos=r_current_pos=1;
    int * buffer= new int[18*N+6*M];
    First=&buffer[0];//new int [N];
    Target=&buffer[N];//new int [M];
    Next=&buffer[N+M];//new int [M];
    r_First=&buffer[N+2*M];// new int[N];
    r_Target=&buffer[2*N+2*M];//new int [M];
    r_Next=&buffer[2*N+3*M];//new int [M];

    affectedQueue=&buffer[2*N+4*M];//new int[N];

    arcQueue=&buffer[3*N+4*M];//new int[2*M];

    levelQueue=&buffer[3*N+6*M];//new int[2*N];

    bucket_first=&buffer[5*N+6*M];//new int[N];
    bucket_target=&buffer[6*N+6*M];//new int[N];
    bucket_next=&buffer[7*N+6*M];//new int[N];
    bucket_last_pos=1;


    idom = &buffer[8*N+6*M];//new int [N];
    level = &buffer[9*N+6*M];//new int [N];
    visited = new bool [N];
    affected = new bool [N];
    label2pre =&buffer[10*N+6*M];// new int[N];
    pre2label =&buffer[11*N+6*M];// new int[N];
    parent = &buffer[12*N+6*M];//new int[N];
    dfsparent =&buffer[13*N+6*M];// new int[N];
    spath = &buffer[14*N+6*M];//new int[N];
    semi =&buffer[15*N+6*M];// new int[N];
    label =&buffer[16*N+6*M];// new int[N];
    dom = &buffer[17*N+6*M];//new int[N];
    for (int i = 0; i < N; i++) {
        bucket_first[i]=bucket_target[i]=bucket_next[i]=0;
        label2pre[i] = pre2label[i] = 0;
        idom[i] = parent[i] = dom[i] = level[i] = 0;
        dfsparent[i] = spath[i] = 0;
        semi[i] = label[i] = i;
        First[i]=r_First[i]=0;
        affected[i] = visited[i] = false;
    }
	for (int i = 0; i < M; i++) {
        Target[i]=Next[i]=r_Target[i] = r_Next[i]= 0;
    }
    level[r] = 1;
    idom[r] = r;
    ccount = cvertices = cedges = 0;
    bucketlevel = N-1;
}

/******************* INSERT - DELETE ARC FROM GRAPH*********************/
inline void insert_arc_to_graph(int x,int y){
    if(First[x]==0){
        Target[current_pos]=y;
        First[x]=current_pos++;
    }
    else{
        Target[current_pos]=y;
        Next[current_pos]=First[x];
        First[x]=current_pos++;
    }
    if(r_First[y]==0){
        r_Target[r_current_pos]=x;
        r_First[y]=r_current_pos++;
    }
    else{
        r_Target[r_current_pos]=x;
        r_Next[r_current_pos]=r_First[y];
        r_First[y]=r_current_pos++;
    }
}

inline void delete_arc_from_graph(int x,int y){
    int i,prev;
    if(Target[First[x]]==y){
        First[x]=Next[First[x]];
    }
    else{
        prev=0;
        i=First[x];
        while(Target[i]!=y){
            prev=i;
            i=Next[i];
        }
        Next[prev]=Next[i];
    }

    if(r_Target[r_First[y]]==x){
        r_First[y]=r_Next[r_First[y]];
    }
    else{
        prev=0;
        i=r_First[y];
        while(r_Target[i]!=x){
            prev=i;
            i=r_Next[i];
        }
                      	  
        r_Next[prev]=r_Next[i];
    }
}


/******************* INSERTION ALGORITHM *********************/

int rootlevel; // level of currently processed affected vertex

// search successors of v for affected vertices
void visit(int v)
{
	int j,selected_node;
    // process edges leaving v
    j=First[v];
    while(j!=0){
		selected_node=Target[j];
        incc();
        if ( level[selected_node] > rootlevel ) {// *j is dominated by subtree root
            incc();
            if (!visited[selected_node]) {
                visited[selected_node] = true;
                levelQueue[last_levelQueue++]=selected_node;
                visit(selected_node);
            }
        }
        else {
            if ( ( level[selected_node] > level[nca] + 1) && (!affected[selected_node]) ) {
                affected[selected_node] = true;
                insertbucket(selected_node);
            }
        }
        j=Next[j];
    }
}

// update levels of visited (but not affected) vertices
void updateLevels() {
    int v;
    while (first_levelQueue<last_levelQueue) {
        incc();
        v = levelQueue[first_levelQueue++];
        level[v] = level[idom[v]]+1;
        visited[v] = false;
    }
}

// update idom and level arrays
inline void updateDomtree() {
    int v;
    while (first_affectedQueue<last_affectedQueue) {
        v = affectedQueue[first_affectedQueue++];
        //printf("pop %d\n",v);
        idom[v] = nca; // new idom
        //if(v<5 || v==15678 )	printf("idom[%d]=%d\n",v,nca);
        level[v] = level[nca] + 1; // update level
        affected[v] = visited[v] = false;
        dfsparent[v] = 0;
    }
    updateLevels();
}


// inserted arc (x,y) is such that both x and y reachable before insertion
inline void insertReachable(int x, int y) {
    int v;

    nca = intersectLevel(x, y);
    if ( (nca == idom[y]) || (nca == y) ) return;

    bucket_last_pos = 1;  // prepare for new sequence of bucket insertions
    affected[y] = true;
    insertbucket(y);
    bucketlevel = level[y];
    while ( (v=getbucket()) ) {
        rootlevel = level[v];
        visited[v] = true;
        //printf("push %d\n",v);
        affectedQueue[last_affectedQueue++]=v;
        visit(v);
    }
    updateDomtree();
}


/******************* BATCH ALGORITHM *********************/
int nextpre; // next preorder number

// depth-first search from node k - visits only previously unreachable vertices
// stores arcs to previously reachable vertices to be processed later
void DFSU(int k) {
    int j,selected_node;

    label2pre[k] = (++nextpre);
    pre2label[nextpre] = k;

    j=First[k];
	while(j!=0){
        incc();
        selected_node=Target[j];
        if (label2pre[selected_node]){
            j=Next[j];
            continue;
        }

        if ( !idom[selected_node] ) {
            DFSU(selected_node);
            parent[label2pre[selected_node]] = label2pre[k];
            dfsparent[selected_node] = k;
        }
        else {
            //fprintf(stderr,"before %d\n",last_arcQueue+2);
            arcQueue[last_arcQueue++]=k;
            arcQueue[last_arcQueue++]=selected_node;
            //fprintf(stderr,"%d\n",last_arcQueue);
            //arcQueue.push(k); arcQueue.push(selected_node);
        }
		j=Next[j];
    }
}

// depth-first search from node k - visits vertices at level > l
void DFSlevel(int k, int l) {
    int j,node_to_visit;

    label2pre[k] = (++nextpre);
    pre2label[nextpre] = k;
    j=First[k];
    while(j!=0){
        incc();
        node_to_visit=Target[j];
        if (label2pre[node_to_visit]){
            j=Next[j];
            continue;       
        }

        if (level[node_to_visit]>l) {
            DFSlevel(node_to_visit,l);
            parent[label2pre[node_to_visit]] = label2pre[k];
            dfsparent[node_to_visit] = k;
        }
        j=Next[j];
    }
}

inline void rcompress (int v, int *parent, int *label, int c) {
    incc();
    int p;
    if ((p=parent[v])>c) {
        rcompress (p, parent, label, c); //does not change parent[v]
      	incc();
      	if (label[p]<label[v]) label[v] = label[p];
      	parent[v] = parent[p];
    }
}

// compute dominator tree rooted at s and consisting of vertices in levels >= l
void snca(int s, int l) {
    //printf("snca...\n");
    int i,j;
	int selected_node;

    nextpre = 0;
    if (l<0) DFSU(s);
    else DFSlevel(s,l);
	
    int N = nextpre;
    for (i=1; i<=N; i++) {
        label[i] = semi[i] = i;
    }

    // process the vertices in reverse preorder
    for (i = N; i > 1; i--) {
        dom[i] = parent[i];
        /*---------------------------------------------
         | check incoming arcs, update semi-dominators
         *--------------------------------------------*/
        int k = pre2label[i];
        j=r_First[k];
        while(j!=0){
            selected_node=r_Target[j];
            int v = label2pre[selected_node]; //v is the source of the arc
            incc();
            if ( (v) && (level[selected_node]>=l) ) {
                int u;
                incc();
                if (v <= i) { u = v; }//v is an ancestor of i
                else {
                    rcompress(v, parent, label, i);
                    u = label[v];
                }
                incc();
                if (semi[u] < semi[i]) {
                    semi[i] = semi[u];
                    spath[k] = selected_node;
                }
            }
            j = r_Next[j];
        }
        label[i] = semi[i];
    }

    /*-----------------------------------------------------------
     | compute dominators using idom[w]=NCA(I,parent[w],sdom[w])
     *----------------------------------------------------------*/
    dom[1] = 1;
    //idom[s] = s;
    for (i = 2; i <= N; i++) {
        int j = dom[i];
        while (j > semi[i]) {
            j = dom[j];
            incc();
        }
        incc();
        dom[i] = j;
        //if (pre2label[i]<5 || pre2label[i]==15678 )printf("idom[%d]=%d --->snca\n",pre2label[i],pre2label[dom[i]]);
        idom[pre2label[i]] = pre2label[dom[i]];
        level[pre2label[i]] = level[pre2label[dom[i]]] + 1;
    }

    // reset
    for (i = 1; i <= N; i++) {
        int k = pre2label[i];
        label2pre[k] = pre2label[i] = parent[i] = dom[i] = 0;
    }
    //printf("EXIT snca\n");
}

// g was previously unreachable, now is at level l

void unreachable(int g) {

    first_arcQueue = 0;
    last_arcQueue = 0;
    //printf("unreachable...\n");
    int u, v;

    snca(g, -1);

    while (first_arcQueue < last_arcQueue) {
        u = arcQueue[first_arcQueue++]; //arcQueue.front(); arcQueue.pop();
        v = arcQueue[first_arcQueue++]; //arcQueue.front(); arcQueue.pop();

        //fprintf(stderr,"pop %d %d\n",u,v);
        insertReachable(u, v);
    }
    //printf("EXIT unreachable\n");
}

void insertArc(int x, int y) {
    if (!idom[x]) return;
    if (idom[y]) insertReachable(x, y); // both x and y reachable
    else { // y was unreachable

        //if(y<5 || y==15678 ) printf("idom[%d]=%d --->insetArc\n",y,x);
        idom[y] = x;
        level[y] = level[x] + 1;
        unreachable(y);
        //printf("insertArc...\n");
    }
}

//print adjacency lists

void printGraph(int * first_arr, int * target_arr, int *next_arr) {
    int i, j;

    fprintf(stderr, "Printing adjacency lists\n");
    for (i = 1; i <= 100; i++) {
        printf("node %d : ", i);
        j = first_arr[i];
        while (j != 0) {
            printf("%d ", target_arr[j]);
            j = next_arr[j];
        }
        printf("\n");
    }
}



/******************* DELETION ALGORITHM *********************/
// checks if y is still reachable after the deletion of (x,y)

bool isReachable(int y) {
    //fprintf(stdout, "begin isReachable %d\n", y);
    int j, node_to_visit;
    int support;
    j = r_First[y];
    while (j != 0) {
        incc();
        node_to_visit = r_Target[j];
        if (!idom[node_to_visit]) {// node_to_visit is unreachable
            j = r_Next[j];
            continue;
        }
        support = intersectLevel(y, node_to_visit);
        if (support != y) { //fprintf(stdout, "end isReachable %d\n", y);
            return true;
        }
        j = r_Next[j];
    }
    //fprintf(stdout, "end isReachable %d\n", y);
    return false;
}

// collect arcs in unreachable subtree to be deleted
// visit vertices reachable from k at level  > l

void DFSclear(int k, int l) {
    int j, node_to_visit;
    label2pre[k] = (++nextpre);
    pre2label[nextpre] = k;

    j = First[k];
    while (j != 0) {
        incc();
        node_to_visit = Target[j];
        if (!label2pre[node_to_visit]) {
            if (level[node_to_visit] > l) {
                DFSclear(node_to_visit, l);
            } else if (!affected[node_to_visit]) {
                //printf("push %d\n",node_to_visit);
                affected[node_to_visit] = true;
                affectedQueue[last_affectedQueue++] = node_to_visit; // store arc target to be processed later
            }
        }
        j = Next[j];
    }
}

inline void deleteReachable(int x, int y) {
    if ((dfsparent[y]) && (x != dfsparent[y]) && (x != spath[y])) return;
    snca(idom[y], level[idom[y]]);
}

inline void deleteUnreachable(int y) {

    //fprintf(stdout, "node %d now unreachable\n", y);

    nextpre = 0;
    DFSclear(y, level[y]);
    int N = nextpre;
    int i, u, z, min;

    min = y;
    while (first_affectedQueue < last_affectedQueue) {

        u = affectedQueue[first_affectedQueue++];
        //printf("pop %d\n",u);
        affected[u] = false;
        z = intersectLevel(u, y);
        //fprintf(stdout, "    u = %d, z = %d\n", u,z);
        if ((z != u) && (level[z] < level[min])) min = z;
    }

    //fprintf(stdout, "min = %d\n", min);

    for (i = N; i >= 1; i--) {
        u = pre2label[i];
        label2pre[u] = pre2label[i] = 0;
        idom[u] = level[u] = 0;
    }

    if (min != y) snca(min, level[min]);
}

void deleteArc(int x, int y) {
    int idomy = idom[y];

    if (!idom[x]) return;

    nca = intersectLevel(x, y);

    if (y == nca) return; // y dominates x - nothing else to do

    if (x == idomy) { // y may become unreachable
        // test if y is reachable from idomy
        if (isReachable(y)) deleteReachable(x, y);
        else deleteUnreachable(y);
    } else deleteReachable(x, y); // y reachable
}

/* print dominator tree */
void printIdom() {
    for (int i = 1; i <= n; i++) {
        printf("idom of node %d = %d - level %d\n", i, idom[i], level[i]);
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


    while (fgets(line, MAXLINE, input) != NULL) {
        switch (line[0]) {
            case '\n':;
            case '\0': break;
            case 'p': if (sscanf(line, "p %d %d %d %d", &n, &m, &r, &dummy) != 4) {
                    fprintf(stderr, "Error reading graph size (%s).\n", file);
                    exit(-1);
                }
                input_file = new int[4 * (m + 1)];
                break;
            case 'a': if (sscanf(line, "a %d %d", &x, &y) != 2) {
                    fprintf(stderr, "Error reading graph arc (%s).\n", file);
                    exit(-1);
                }
                input_file[current_input_pos++] = x;
                input_file[current_input_pos++] = y;
                input_file[current_input_pos++] = INPUT_a;
                break;
            case 'e': fprintf(stderr, "read e\n");
                input_file[current_input_pos++] = 0;
                input_file[current_input_pos++] = 0;
                input_file[current_input_pos++] = INPUT_e;
		//printf("\n !!!\n");
                break;
            case 'i': if (sscanf(line, "i %d %d", &x, &y) != 2) {
                    fprintf(stderr, "Error reading graph insertion (%s).\n", file);
                    exit(-1);
                }
                input_file[current_input_pos++] = x;
                input_file[current_input_pos++] = y;
                input_file[current_input_pos++] = INPUT_i;
                break;
            case 'd': if (sscanf(line, "d %d %d", &x, &y) != 2) {
                    fprintf(stderr, "Error reading graph deletion (%s).\n", file);
                    exit(-1);
                }
                input_file[current_input_pos++] = x;
                input_file[current_input_pos++] = y;
                input_file[current_input_pos++] = INPUT_d;
                break;
            default: fprintf(stderr, "Error reading graph (%s).\n", file);
                exit(-1);
        }
    }

    fprintf(stderr, "END reading graph (%s).\n", file);
    fclose(input);
}


// process input arcs

void processInput() {
    int input_source, input_target, input_type;
    int current_input_pos;
    for (current_input_pos = 0; current_input_pos <= 3 * m; current_input_pos += 3) {
        input_source = input_file[current_input_pos];
        input_target = input_file[current_input_pos + 1];
        input_type = input_file[current_input_pos + 2];
        switch (input_type) {
            case INPUT_a:
                insert_arc_to_graph(input_source, input_target);
                break;
            case INPUT_e: //fprintf(stderr,"read e\n");
                first_arcQueue = last_arcQueue = first_affectedQueue = last_affectedQueue = first_levelQueue = last_levelQueue = 0;
                unreachable(r); // compute dominator tree from r
                //checkLevels(); checkNCA();
                break;
            case INPUT_i:// fprintf(stderr,"insert %d,%d \n", input_source, input_target);
                first_arcQueue = last_arcQueue = first_affectedQueue = last_affectedQueue = first_levelQueue = last_levelQueue = 0;
                insert_arc_to_graph(input_source, input_target);
                insertArc(input_source, input_target); // run the algorithm for every new arc
                //checkLevels(); checkNCA();
                break;
            case INPUT_d: //fprintf(stderr,"delete %d,%d \n", input_source, input_target;
                first_arcQueue = last_arcQueue = first_affectedQueue = last_affectedQueue = first_levelQueue = last_levelQueue = 0;
                delete_arc_from_graph(input_source, input_target);
                deleteArc(input_source, input_target);
                //checkLevels(); checkNCA();
                break;
            default: fprintf(stderr, "Error reading graph.\n");
                exit(-1);
        }
    }
}

void cleanUp() {
    delete [] buffer;
    /*  delete [] affectedQueue;
        delete [] arcQueue;
        delete [] First;
        delete [] Target;
        delete [] Next;
        delete [] r_First;
        delete [] r_Target;
        delete [] r_Next;
        delete [] bucket_first;
        delete [] bucket_target;
        delete [] bucket_next;
        delete [] bucket_last;
        delete [] label2pre;
        delete [] pre2label;
        delete [] idom;
        delete [] level;
        delete [] parent;
        delete [] dfsparent;
        delete [] spath;
        delete [] semi;
        delete [] label;
        delete [] dom;
     */
    delete [] visited;
    delete [] affected;
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        printf("\n usage: %s <input file>\n\n", argv[0]);
        exit(-1);
    }

    char *file = argv[1];

    readGraph(file);

    RFWTimer timer(true);
    double t;
    init(n + 1, m + 1);
    processInput();
    cleanUp();
    t = timer.getTime();

   // printIdom();

    printf("%g\n ", t);

    return 0;
}
