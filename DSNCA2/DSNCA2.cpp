/*---------------------------------------------------------------
 | Dynamic version of SNCA
 | - computation is repeated if for the new arc (x,y) only if
 |   x is reachable from r
 | - DFS is not performed if the new arc does not invalidate
 |   previous DFS tree
 | - if previous DFS tree is still valid the computation of sdoms
 |   is repeated for vertices with label2pre < label2pre[y]
 *---------------------------------------------------------------*/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "rfw_timer.h"

using namespace std;

#define MAXLINE       100   /* max length of input line */
#define INPUT_a 0
#define INPUT_i 1
#define INPUT_d 2
#define INPUT_e 3

char line[MAXLINE]; /* stores input line */

int *input_file; // stores input arcs

int n, m; /* number of nodes, arcs */

int *First;
int *Target;
int *Next;
int *r_First;
int *r_Target;
int *r_Next;
int current_pos;
int r_current_pos;

int r; // source
int nr; //number of vertices reachable from r

int *label2pre; // mapping node id -> preoder number
int *pre2label; // mapping preoder number -> node id
int *label2post; // mapping node id -> postorder number
int *idom; // dominator tree
int *parent; // parents in the link-eval tree
int *dfsparent; // parents in DFS tree
int nextpre; // next preorder number
int nextpost; // next postorder number

int *spath; // predecessors from sdom-paths

int *semi;
int *label;
int *dom;

int count; // comparison counter
// increment traversal counter
inline void incc() { }//count++; }

bool valid; // is dfs tree valid?

/* depth-first search from node k
   assigns postorder numbers */
void DFS(int k) {
    int j,node_to_visit;

    label2pre[k] = (++nextpre);
    pre2label[nextpre] = k;

    j=First[k];
    while(j!=0){
        node_to_visit=Target[j];
        incc();
        if (!label2pre[node_to_visit]) {
            DFS(node_to_visit);
            parent[label2pre[node_to_visit]] = label2pre[k];
            dfsparent[label2pre[node_to_visit]] = label2pre[k];
        }
        j=Next[j];
    }

    label2post[k] = ++nextpost;
}

/* initialization  */
void init(int N,int M) {
    int i;

    //fprintf(stderr,"\n initializing n=%d\n",N);
    nextpre = nextpost = 0;
    count = 0;

    current_pos=r_current_pos=1;
    First= new int[N];
    Target=new int [M];
    Next=new int [M];
    r_First= new int[N];
    r_Target=new int [M];
    r_Next=new int [M];

    label2pre = new int[N];
    pre2label = new int[N];
    label2post = new int[N];
    idom = new int[N];
    parent = new int[N];
    dfsparent = new int[N];
    semi = new int[N];
    label = new int[N];
    dom = new int[N];
    spath = new int [N];

    for (i = 0; i < N; i++) {

        label2pre[i] = pre2label[i] = label2post[i] = 0;
        idom[i] = parent[i] = dfsparent[i] = 0;
        dom[i] = spath[i] = 0;
        semi[i] = label[i] = i;
        First[i]=r_First[i]=0;
    }
    for (int i = 0; i < M; i++) {
        Target[i]=Next[i]=r_Target[i] = r_Next[i]=0;
    }
    nr=1;
    valid = true;
}

inline void insert_arc(int x,int y){
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

inline void delete_arc(int x,int y){
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

/* reset arrays and counters */
inline void fullreset()
{
    int j;
    for (int i=0; i<=nr; i++)
    {
        j = pre2label[i];
        label2pre[j] = pre2label[i] = label2post[j] = 0;
        parent[i] = dfsparent[i] = 0;
        label[i] = semi[i] = i;
        dom[i] = spath[i] = 0;
    }
    nextpre = nextpost = 0;
    DFS(r);
    nr = nextpre;
    valid = true;
}

// reset structures for vertices with label2pre <= k
inline void partialreset(int k)
{
    for (int i=0; i<=k; i++)
    {
        dom[i] = parent[i] = dfsparent[i];
        label[i] = semi[i] = i;
        spath[i] = 0;
    }
    for (int i=k+1; i<=nr; i++)
    {
        dom[i] = parent[i] = dfsparent[i];
        label[i] = semi[i];
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


void snca(int r, int y) {

    int l;
    if (y>0)
    {
        l = label2pre[y];
        partialreset(l);
    }
    else
    {
        fullreset();
        l = nr;
    }
    int N = nr;

    int i,j;

    // process the vertices in reverse preorder
    for (i = l; i > 1; i--) {
        dom[i] = parent[i];
        /*---------------------------------------------
         | check incoming arcs, update semi-dominators
         *--------------------------------------------*/
        int k = pre2label[i];
        j=r_First[k];
        while(j!=0){
            int v = label2pre[r_Target[j]]; //v is the source of the arc
            incc();
            if (v) {
                int u;
                incc();
                if (v <= i) { u = v; }//v is an ancestor of i
                else {
                    rcompress(v, parent, label, i);
                    u = label[v];
                }
                incc();
                if (semi[u] < semi[i]) { semi[i] = semi[u]; spath[i] = v; }
            }
            j=r_Next[j];
        }
        label[i] = semi[i];
    }

    /*-----------------------------------------------------------
     | compute dominators using idom[w]=NCA(I,parent[w],sdom[w])
     *----------------------------------------------------------*/
    dom[1] = 1;
    //idom[r] = r;
    for (i=2; i<=N; i++) {
	j = dom[i];
	while (j>semi[i]) {j=dom[j]; incc();}
	incc();
	dom[i] = j;
	//idom[pre2label[i]] = pre2label[dom[i]];
    }
}

// Translate dominators from DFS numbers to original vertex labels
inline void translateDom()
{
    idom[r] = r;
    for (int i = 2; i <= nr; i++) idom[pre2label[i]] = pre2label[dom[i]];
}

/* print dominator tree */
void printIdom()
{
    translateDom();
    printf("\n");
    for (int i = 1; i <= n; i++) {
        printf("idom of node %d = %d\n", i, idom[i]);
    }
}

// compute nearest common ancestor of v1 and v2 in dom tree
inline int intersect (int v1, int v2)
{
    //printf("\n start intersect \n");
    do {
        incc(); //outer test
        while (v1>v2) {incc(); v1 = dom[v1];}
        incc(); //failed above
	while (v2>v1) {incc(); v2 = dom[v2];}
	incc(); //failed above
    } while (v1!=v2);
    //printf("\n end intersect \n");
    return v1;
}

/* read graph from input file */
void readGraph(const char *file) {
    FILE *input = fopen(file, "r");
    if (!input) {
        fprintf(stderr, "Error opening file \"%s\".\n", file);
        exit(-1);
    }

    int x, y, dummy;
    int current_input_pos=0;


    while (fgets(line, MAXLINE, input) != NULL) {
        switch (line[0]) {
            case '\n':;
            case '\0': break;
            case 'p': if (sscanf(line, "p %d %d %d %d", &n, &m, &r, &dummy) != 4) {
                    fprintf(stderr, "Error reading graph size (%s).\n", file);
                    exit(-1);
                }
                input_file=new int[5*(m+1)];
                break;
            case 'a': if (sscanf(line, "a %d %d", &x, &y) != 2) {
                    fprintf(stderr, "Error reading graph arc (%s).\n", file);
                    exit(-1);
                }
                input_file[current_input_pos++] = x;
                input_file[current_input_pos++] = y;
                input_file[current_input_pos++] = INPUT_a;
                break;
            case 'e': fprintf(stderr,"read e\n");
                input_file[current_input_pos++] = 0;
                input_file[current_input_pos++] = 0;
                input_file[current_input_pos++] = INPUT_e;
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
    int i,j;
    int input_source,input_target,input_type;
    int current_input_pos;
    for (current_input_pos=0 ; current_input_pos <= 3*m ; current_input_pos+=3){
        input_source=input_file[current_input_pos];
        input_target=input_file[current_input_pos+1];
        input_type=input_file[current_input_pos+2];
        switch (input_type) {
            case INPUT_a: 
                      insert_arc(input_source,input_target);

                      break;
            case INPUT_e: //fprintf(stderr,"read e\n");
                      snca(r,-1); // compute dominator tree until current edge
                      break;
            case INPUT_i:// fprintf(stderr,"insert %d,%d \n", input_source, input_target);

                      insert_arc(input_source,input_target);

                      i = label2pre[input_source];
                      j = label2pre[input_target];

                      if ( (input_source==r)||(i) ) // source is reachable
                      {
                            if (j) // target is reachable
                            {
                                // is dfs tree valid?
                                if ( ( label2pre[input_source] < label2pre[input_target] ) && ( label2post[input_source] < label2post[input_target] ) ) valid = false;

                                int k = intersect(i,j);
                                if ( (k != dom[j]) && (k != j) ) // dom[j] is not an ancestor of i
                                {
                                    if (!valid)
                                    {
                                        // dfs tree is invalid; run from scratch
                                        snca(r,-1);
                                    }
                                    else
                                    {
                                        snca(r,input_target);
                                    }
                                }
                            }
                            else
                            {
                                // target was unreachable; run from scratch
                                snca(r,-1);
                            }
                      }
                      break;
            case INPUT_d: //fprintf(stderr,"delete %d,%d \n",input_source, input_target);
                      delete_arc(input_source,input_target);
                      i = label2pre[input_source];
                      j = label2pre[input_target];
                      if (i) // source is reachable so target was reachable before the edge deletion
                      {
                            if ( i == dfsparent[j] ) snca(r,-1);
                            else if ( i == spath[j] ) snca(r,input_target);
                      }
                      break;
            default: fprintf(stderr, "Error reading graph.\n");
                     exit(-1);
        }
    }
}

void printLabels() {
    int i;

    printf("\n");
    for (i = 1; i <= n; i++) {
        printf("node %d : preorder = %d, postorder = %d, dom = %d\n", i, label2pre[i], label2post[i], dom[i]);
    }
}

int main(int argc, char *argv[]) {
    //int i;
    if (argc != 2) {
        printf("\n usage: %s <input file>\n\n", argv[0]);
        exit(-1);
    }

    char *file = argv[1];
    //r = 1;

    //int K=10;
    readGraph(file);
    RFWTimer timer(true);
    double t;
    //for (int i=1; i<=K; i++){
        init(n+1,m+1);
        processInput();
        
    //}
    t=timer.getTime();
    //printGraph(adj);
    //printGraph(radj);

   // printIdom();
    //printLabels();

    //printf("\n comparisons = %d\n ", count);
    printf("%lg\n ", t);

    return 0;
}
