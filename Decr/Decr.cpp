/*---------------------------------------------------------------
| Dynamic Dominators - Depth Based Search algorithm
| uses SNCA for batch processing
*---------------------------------------------------------------*/

#ifdef _WIN32
	#include <chrono>
#elif _linux
	#include "rfw_timer.h"
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <cmath>
#include <limits.h>

using namespace std;

#define MAXLINE       100   /* max length of input line */
#define INPUT_a 0
#define INPUT_i 1
#define INPUT_d 2 
#define INPUT_e 3
#define T 1.4

#define UPDATE_LOW_HIGH 0 // 0 -> updates LowHigh, 1 -> just decremental algo

struct representative{
	int representativesName;
	int leaves;
	unsigned long int tag;

	struct node* nodesListHead;
	struct node* nodesListTail;
	struct representative* leftRepresentative;
	struct representative* rightRepresentative;
};

struct node{
	int nodesName;
	unsigned long int tag;

	struct node* leftNode;
	struct node* rightNode;
	struct representative* rep;
};

struct node** nodesTablePreorder;
struct node** nodesTablePostorder;
struct representative* representativesListHeadPreorder;
struct representative* representativesListTailPostorder;
int representativesCounterPreorder;
int representativesCounterPostorder;
int nodesPerRepresentative;
unsigned long int tagSize;

char line[MAXLINE]; /* stores input line */
int *input_file; // stores input arcs
int r; // source
int n, m; /* number of nodes, arcs */
int *buffer;

// input graph representation
// dynamic adjacency lists for forward and reverse graphneighbour
int *First;         // position of first out-neighbor
int *Target;        // stores out-neighbors
int *Next;          // position of next out-neighbor
int *r_First;       // position of first in-neighbor
int *r_Target;      // stores in-neighbors
int *r_Next;        // position of next in-neighbor
int *label2pre; // mapping node id -> preoder number
int *pre2label; // mapping preoder number -> node id
int *parent; // parents in the link-eval tree
int *semi;
int *label;
int *dom;
int *spath; // predecessors from sdom-paths
int *dfsparent; // parents in DFS tree

int current_pos;    // next available position in Target
int r_current_pos;  // next available position in r_Target
int nca; // nearest common ancestor of updated edge endpoints
int nextpre; // next preorder number

/******************* BUCKET STRUCTURE *********************/
int *level; // level array
int *idom; // dominator tree
bool *visited; // true for visited vertices

int *arcQueue; // stores (possibly) affected vertices
int last_arcQueue;

/* ====== new variables ====== */
char file[100];

int *size; // number of descendants for each node in D
int *preorder2labelDominator;
int *label2preorderDominator;
int *dominatorFirst;
int *dominatorTarget;
int *dominatorNext;
int *dfsDominatorDiscovered;
int *derivedOutFirst;
int *derivedOutTarget;
int *derivedOutNext;
int *derivedOutPrev;
int *derivedInFirst;
int *derivedInTarget;
int *derivedInNext;
int *derivedInPrev;
int *derivedEdgeCounter;
int *derivedGraphInSiblings;
int *triples;
int *QList;
int *inQList;
int *criticalPath;
int *topologicalOrder;
int *lowHighHead;
int *lowHighPrevNode;
int *lowHighNextNode;
int *derivedOutLowHighFirst;
int *derivedOutLowHighTarget;
int *derivedOutLowHighPrev;
int *derivedOutLowHighNext;
int *violatingLowHigh;
int *needUpdateLowHigh;
int *needUpdateLowHighSorted;
int *prevIdom;
int *positionInViolatingLowHigh;
int *derivedOutFirstReverse;
int *derivedInFirstReverse;
int *derivedOutLowHighFirstReverse;
int *visitedNodes;
int *nodesInAlreadyCheckedList;
int *derivedInLowHighReverseNode;

int **derivedInLowHigh;
int **derivedInLowHighReversePosition;

unsigned long int *lowHighId;

bool *derivedArcFromDominator;
bool *inLowHighOrder;
bool *inLowHighChildrenList;
bool *inViolatingLowHigh;
bool *inNeedUpdateLowHigh;
bool *inNeedUpdateLowHighSorted;

int dfsDominatorCounter;
int triplesCounter;
int derivedGraphCurrentPosition;
int QListCounter;
int nodesInQList;
int criticalPathCounter;
int lastNodePreorder;
int lastNodePostorder;
int prevLevel;
int alreadyCheckedCurrentPosition;
int topologicalOrderCounter;
int derivedOutLowHighCurrentPosition;
int violatingLowHighCounter;
int needUpdateLowHighCounter;
int needUpdateLowHighSortedCounter;
int visitedNodesCounter;
int nodesInAlreadyCheckedListCounter;

unsigned long int maxId;

bool criticalPathFlag;
bool noNewParentFlag;
bool violatingLowHighFlag;
bool executeProcessNeedUpdateLowHighFlag;

long double representativeIdStep;
long double nextRepresentativeIdPreorder;
long double nextRepresentativeIdPostorder;
/* ============================================*/

struct node* createNewNode(int name){
	struct node* tmpNode= (struct node*)malloc(sizeof(struct node));

	tmpNode->nodesName= name;
	tmpNode->tag= 0;
	tmpNode->leftNode= NULL;
	tmpNode->rightNode= NULL;
	tmpNode->rep= NULL;

	return tmpNode;
}

struct representative* createNewRepresentative(int name){
	struct representative* tmpRep= (struct representative*)malloc(sizeof(struct representative));

	tmpRep->representativesName= name;
	tmpRep->tag= 0;
	tmpRep->leaves= 0;
	tmpRep->nodesListHead= NULL;
	tmpRep->nodesListTail= NULL;
	tmpRep->leftRepresentative= NULL;
	tmpRep->rightRepresentative= NULL;

	return tmpRep;
}

// compute nearest common ancestor
inline int intersectLevel(int v1, int v2){
	int x= v1;
	int y= v2;

	if(v1 == 0) return y;
	if(v2 == 0) return x;
	while(v1 != v2){
		if(level[v1] >= level[v2]) v1= idom[v1];
		if(level[v2]> level[v1]) v2= idom[v2];
	}

	return v1;
}

void resetTriples(){
	int nodes= n+1;
	int edges= m+1;
	triplesCounter= 0;

	for(int i= (3*nodes+3*edges)-1; i >= 0; i--){
		triples[i]= 0;
	}
}

// initialization
void init(int N,int M) {
	current_pos=r_current_pos=1;
	int * buffer= new int[37*N+26*M];

	First=&buffer[0];//new int [N];
	Target=&buffer[N];//new int [M];
	Next=&buffer[N+M];//new int [M];
	r_First=&buffer[N+2*M];// new int[N];
	r_Target=&buffer[2*N+2*M];//new int [M];
	r_Next=&buffer[2*N+3*M];//new int [M];

	arcQueue=&buffer[2*N+4*M];//new int[2*M];
	idom = &buffer[2*N+6*M];//new int [N];
	level = &buffer[3*N+6*M];//new int [N];

	label2pre =&buffer[4*N+6*M];// new int[N];
	pre2label =&buffer[5*N+6*M];// new int[N];

	parent = &buffer[6*N+6*M];//new int[N];
	dfsparent =&buffer[7*N+6*M];// new int[N];
	spath = &buffer[8*N+6*M];//new int[N];
	semi =&buffer[9*N+6*M];// new int[N];
	label =&buffer[10*N+6*M];// new int[N];
	dom = &buffer[11*N+6*M];//new int[N];
	size= &buffer[12*N+6*M];//new int[N];

	preorder2labelDominator= &buffer[13*N+6*M];//new int[N];
	label2preorderDominator= &buffer[14*N+6*M];//new int[N];

	dominatorFirst= &buffer[15*N+6*M];//new int[N];
	dominatorTarget= &buffer[16*N+6*M];//new int[N];
	dominatorNext= &buffer[17*N+6*M];//new int[N];
	dfsDominatorDiscovered= &buffer[18*N+6*M];//new int[N];

	derivedOutFirst= &buffer[19*N+6*M];//new int[N];
	derivedOutTarget= &buffer[20*N+6*M];//new int[M];
	derivedOutNext= &buffer[20*N+7*M];//new int[M];
	derivedOutPrev= &buffer[20*N+8*M];//new int[M];
	derivedInFirst= &buffer[20*N+9*M];//new int[N];
	derivedInTarget= &buffer[21*N+9*M];//new int[M];
	derivedInNext= &buffer[21*N+10*M];//new int[M];
	derivedInPrev= &buffer[21*N+11*M];//new int[M];
	derivedEdgeCounter= &buffer[21*N+12*M];//new int[M];
	derivedGraphInSiblings= &buffer[21*N+13*M];//new int[N];

	topologicalOrder= &buffer[22*N+13*M];//new int[N];

	lowHighHead= &buffer[23*N+13*M];//new int[N];
	lowHighPrevNode= &buffer[24*N+13*M];//new int[N];
	lowHighNextNode= &buffer[25*N+13*M];//new int[N];

	derivedOutLowHighFirst= &buffer[26*N+13*M];//new int[N];
	derivedOutLowHighTarget= &buffer[27*N+13*M];//new int[2*M];
	derivedOutLowHighPrev= &buffer[27*N+15*M];//new int[2*M];
	derivedOutLowHighNext= &buffer[27*N+17*M];//new int[2*M];

	violatingLowHigh= &buffer[27*N+19*M];//new int[N];
	needUpdateLowHigh= &buffer[28*N+19*M];//new int[N];
	needUpdateLowHighSorted= &buffer[29*N+19*M];//new int[N];
	prevIdom= &buffer[30*N+19*M];//new int[N];
	positionInViolatingLowHigh= &buffer[31*N+19*M];//new int[N];

	derivedOutFirstReverse= &buffer[32*N+19*M];//new int[M];
	derivedInFirstReverse= &buffer[32*N+20*M];//new int[M];
	derivedOutLowHighFirstReverse= &buffer[32*N+21*M];//new int[M];

	visitedNodes= &buffer[32*N+22*M];//new int[N];
	nodesInAlreadyCheckedList= &buffer[33*N+22*M];//new int[N];
	derivedInLowHighReverseNode= &buffer[34*N+22*M];//new int[M];
	triples= &buffer[34*N+23*M];//new int[3*N+3*M];

	QList= new int[N];//new int[N];
	inQList= new int[N];//new int[N];
	criticalPath= new int[N];//new int[N];

	lowHighId= new unsigned long int[N];//new unsigned long int[N];

	visited = new bool[N];
	derivedArcFromDominator= new bool[N];//new bool[N];
	inLowHighOrder= new bool[N];//new bool[N];
	inLowHighChildrenList= new bool[N];//new bool[N];
	inViolatingLowHigh= new bool[N];//new bool[N];
	inNeedUpdateLowHigh= new bool[N];//new bool[N];
	inNeedUpdateLowHighSorted= new bool[N];//new bool[N];

	derivedInLowHigh= new int*[N];
	derivedInLowHighReversePosition= new int*[N];
	for(int i= n; i >= 0; i--){
		derivedInLowHigh[i]=  new int[2];
		derivedInLowHighReversePosition[i]=  new int[2];
	}

	for(int i= n; i >= 0; i--){
		label2pre[i]= pre2label[i]= 0;
		idom[i]= parent[i]= dom[i]= level[i]= 0;
		dfsparent[i]= spath[i]= 0;
		semi[i]= label[i]= i;
		First[i]= r_First[i]= 0;
		size[i]= 1;
		preorder2labelDominator[i]= 0;
		label2preorderDominator[i]= 0;
		dominatorFirst[i]= 0;
		dominatorTarget[i]= dominatorNext[i]= 0;
		dfsDominatorDiscovered[i]= 0;
		derivedOutFirst[i]= 0;
		derivedInFirst[i]= 0;
		derivedGraphInSiblings[i]= 0;
		QList[i]= 0;
		inQList[i]= 0;
		criticalPath[i]= 0;
		topologicalOrder[i]= 0;
		lowHighHead[i]= 0;
		lowHighPrevNode[i]= 0;
		lowHighNextNode[i]= 0;
		lowHighId[i]= 0;
		derivedInLowHigh[i][0]= 0;
		derivedInLowHigh[i][1]= 0;
		derivedInLowHighReversePosition[i][0]= 0;
		derivedInLowHighReversePosition[i][1]= 0;
		derivedOutLowHighFirst[i]= 0;
		violatingLowHigh[i]= 0;
		needUpdateLowHigh[i]= 0;
		needUpdateLowHighSorted[i]= 0;
		prevIdom[i]= 0;
		positionInViolatingLowHigh[i]= 0;
		visitedNodes[i]= 0;
		nodesInAlreadyCheckedList[i]= 0;

		visited[i]= false;
		derivedArcFromDominator[i]= false;
		inLowHighOrder[i]= false;
		inLowHighChildrenList[i]= false;
		inViolatingLowHigh[i]= false;
		inNeedUpdateLowHigh[i]= false;
		inNeedUpdateLowHighSorted[i]= false;
	}

	for(int i= m; i >= 0; i--) {
		Target[i]=Next[i]=r_Target[i] = r_Next[i]= 0;
		derivedOutTarget[i]= derivedOutNext[i]= derivedOutPrev[i]= derivedEdgeCounter[i]= 0;
		derivedInTarget[i]= derivedInNext[i]= derivedInPrev[i]= 0;
		derivedOutLowHighTarget[i]= derivedOutLowHighNext[i]= derivedOutLowHighPrev[i]= 0;
		derivedOutFirstReverse[i]= derivedInFirstReverse[i]= derivedOutLowHighFirstReverse[i]= 0;
		derivedInLowHighReverseNode[i]= 0;
	}
	for(int i= M; i < 2*M; i++){
		derivedOutLowHighTarget[i]= derivedOutLowHighNext[i]= derivedOutLowHighPrev[i]= 0;
	}

	resetTriples();

	QListCounter= 0;
	nodesInQList= 0;
	criticalPathCounter= 0;
	violatingLowHighCounter= 0;
	lastNodePreorder= 0;
	lastNodePostorder= 0;
	needUpdateLowHighCounter= 0;
	needUpdateLowHighSortedCounter= 0;
	visitedNodesCounter= 0;
	nodesInAlreadyCheckedListCounter= 0;

	level[r]= 1;
	dfsDominatorCounter= 1;
	derivedGraphCurrentPosition= 1;
	derivedOutLowHighCurrentPosition= 1;
	alreadyCheckedCurrentPosition= 1;

	criticalPathFlag= false;
	noNewParentFlag= false;
	violatingLowHighFlag= false;
	executeProcessNeedUpdateLowHighFlag= false;

	idom[r]= r;
	topologicalOrderCounter= n-1;

	nodesTablePreorder= (struct node**)malloc(N*sizeof(struct node*));
	nodesTablePostorder= (struct node**)malloc(N*sizeof(struct node*));

	for(int i= n; i >= 0; i--){
		nodesTablePreorder[i]= NULL;
		nodesTablePostorder[i]= NULL;
	}

	representativesListHeadPreorder= NULL;
	representativesListTailPostorder= NULL;
	representativesCounterPreorder= 0;
	representativesCounterPostorder= 0;
	nodesPerRepresentative= (int) (log(N)/log(2));
	tagSize= 2;

	maxId= ULLONG_MAX/4;
	representativeIdStep= (long double)(maxId)/(long double)(N/(nodesPerRepresentative/2));
	nextRepresentativeIdPreorder= representativeIdStep;
	nextRepresentativeIdPostorder= representativeIdStep;
}

void createPreorderList(int newNodePreorder){
	struct representative* tmpRep= NULL;
	struct representative* newRep= NULL;
	struct representative* currentRep= NULL;
	struct node* tmpNode= NULL;
	struct node* midNode= NULL;
	struct node* currentNode= NULL;
	int counter= 0;

	if(representativesListHeadPreorder == NULL){
		tmpRep= createNewRepresentative(newNodePreorder);
		representativesListHeadPreorder= tmpRep;
		tmpRep->tag= 0;

		tmpNode= createNewNode(newNodePreorder);
		tmpNode->rep= tmpRep;
		tmpNode->tag= 0;

		tmpRep->nodesListHead= tmpNode;
		tmpRep->nodesListTail= tmpNode;
		tmpRep->leaves++;

		nodesTablePreorder[newNodePreorder]= tmpNode;
		lastNodePreorder= newNodePreorder;
		return;
	}

	tmpNode= createNewNode(newNodePreorder);
	tmpRep= nodesTablePreorder[lastNodePreorder]->rep;

	if(tmpRep->leaves == nodesPerRepresentative){
		newRep= createNewRepresentative(newNodePreorder);

		newRep->tag= (unsigned long int) (floor(nextRepresentativeIdPreorder));
		nextRepresentativeIdPreorder+= representativeIdStep;
		newRep->leftRepresentative= tmpRep;
		tmpRep->rightRepresentative= newRep;

		midNode= tmpRep->nodesListHead;
		while(counter != tmpRep->leaves/2){
			midNode= midNode->rightNode;
			counter++;
		}
		newRep->representativesName= midNode->nodesName;

		midNode->leftNode->rightNode= NULL;
		midNode->leftNode= NULL;
		newRep->nodesListHead= midNode;

		tmpRep->leaves= counter;
		newRep->leaves= nodesPerRepresentative-counter;

		currentNode= tmpRep->nodesListHead;
		currentNode->tag= 0;
		currentNode= currentNode->rightNode;
		while(currentNode != NULL){
			currentNode->tag= currentNode->leftNode->tag+(1LL << (nodesPerRepresentative-tmpRep->leaves));

			if(currentNode->rightNode == NULL) tmpRep->nodesListTail= currentNode;
			currentNode= currentNode->rightNode;
		}

		currentNode= newRep->nodesListHead;
		currentNode->tag= 0;
		currentNode->rep= newRep;
		currentNode= currentNode->rightNode;		
		while(currentNode != NULL){
			currentNode->tag= currentNode->leftNode->tag + (1LL << (nodesPerRepresentative-newRep->leaves));
			currentNode->rep= newRep;

			if(currentNode->rightNode == NULL) newRep->nodesListTail= currentNode;
			currentNode= currentNode->rightNode;
		}
	}

	currentNode= nodesTablePreorder[lastNodePreorder];
	tmpNode->rep= currentNode->rep;
	tmpNode->tag= currentNode->tag+(1LL << (nodesPerRepresentative-currentNode->rep->leaves));

	tmpNode->leftNode= currentNode;
	currentNode->rightNode= tmpNode;
	tmpNode->rep->nodesListTail= tmpNode;

	tmpNode->rep->leaves++;

	nodesTablePreorder[newNodePreorder]= tmpNode;
	lastNodePreorder= newNodePreorder;
}

void createPostorderList(int newNodePostorder){
	struct representative* tmpRep= NULL;
	struct representative* newRep= NULL;
	struct representative* currentRep= NULL;
	struct node* tmpNode= NULL;
	struct node* midNode= NULL;
	struct node* currentNode= NULL;
	int counter= 0;

	if(representativesListTailPostorder == NULL){
		tmpRep= createNewRepresentative(newNodePostorder);
		representativesListTailPostorder= tmpRep;
		tmpRep->tag= 0;

		tmpNode= createNewNode(newNodePostorder);
		tmpNode->rep= tmpRep;
		tmpNode->tag= 0;

		tmpRep->nodesListHead= tmpNode;
		tmpRep->nodesListTail= tmpNode;
		tmpRep->leaves++;

		nodesTablePostorder[newNodePostorder]= tmpNode;
		lastNodePostorder= newNodePostorder;
		return;
	}

	tmpNode= createNewNode(newNodePostorder);
	tmpRep= nodesTablePostorder[lastNodePostorder]->rep;

	if(tmpRep->leaves == nodesPerRepresentative){
		newRep= createNewRepresentative(newNodePostorder);
		representativesListTailPostorder= newRep;

		newRep->tag= (unsigned long int) (floor(nextRepresentativeIdPostorder));
		nextRepresentativeIdPostorder+= representativeIdStep;
		newRep->leftRepresentative= tmpRep;
		tmpRep->rightRepresentative= newRep;

		midNode= tmpRep->nodesListHead;
		while(counter != tmpRep->leaves/2){
			midNode= midNode->rightNode;
			counter++;
		}
		newRep->representativesName= midNode->nodesName;

		midNode->leftNode->rightNode= NULL;
		midNode->leftNode= NULL;
		newRep->nodesListHead= midNode;

		tmpRep->leaves= counter;
		newRep->leaves= nodesPerRepresentative-counter;

		currentNode= tmpRep->nodesListHead;
		currentNode->tag= 0;
		currentNode= currentNode->rightNode;
		while(currentNode != NULL){
			currentNode->tag= currentNode->leftNode->tag+(1LL << (nodesPerRepresentative-tmpRep->leaves));

			if(currentNode->rightNode == NULL) tmpRep->nodesListTail= currentNode;
			currentNode= currentNode->rightNode;
		}

		currentNode= newRep->nodesListHead;
		currentNode->tag= 0;
		currentNode->rep= newRep;
		currentNode= currentNode->rightNode;
		while(currentNode != NULL){
			currentNode->tag= currentNode->leftNode->tag + (1LL << (nodesPerRepresentative-newRep->leaves));
			currentNode->rep= newRep;

			if(currentNode->rightNode == NULL) newRep->nodesListTail= currentNode;
			currentNode= currentNode->rightNode;
		}
	}

	currentNode= nodesTablePostorder[lastNodePostorder];
	tmpNode->rep= currentNode->rep;
	tmpNode->tag= currentNode->tag+(1LL << (nodesPerRepresentative-currentNode->rep->leaves));

	tmpNode->leftNode= currentNode;
	currentNode->rightNode= tmpNode;
	tmpNode->rep->nodesListTail= tmpNode;

	tmpNode->rep->leaves++;

	nodesTablePostorder[newNodePostorder]= tmpNode;
	lastNodePostorder= newNodePostorder;
}

/******************* INSERT - DELETE ARC FROM GRAPH*********************/
inline void insert_arc_to_graph(int x,int y){
	if(First[x] == 0){
		Target[current_pos]=y;
		First[x]=current_pos++;
	}
	else{
		Target[current_pos]=y;
		Next[current_pos]=First[x];
		First[x]=current_pos++;
	}
	if(r_First[y] == 0){
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
	if(Target[First[x]] == y){
		First[x]=Next[First[x]];
	}
	else{
		prev=0;
		i=First[x];
		while(Target[i] != y){
			prev=i;
			i=Next[i];
		}
		Next[prev]=Next[i];
	}

	if(r_Target[r_First[y]] == x){
		r_First[y]=r_Next[r_First[y]];
	}
	else{
		prev=0;
		i=r_First[y];
		while(r_Target[i] != x){
			prev=i;
			i=r_Next[i];
		}

		r_Next[prev]=r_Next[i];
	}
}

/******************* BATCH ALGORITHM *********************/
// depth-first search from node k - visits only previously unreachable vertices
// stores arcs to previously reachable vertices to be processed later
void DFSU(int k) {
	int j,selected_node;

	label2pre[k] = (++nextpre);
	pre2label[nextpre] = k;

	j=First[k];
	while(j != 0){
		selected_node=Target[j];
		if(label2pre[selected_node]){
			j=Next[j];
			continue;
		}

		if(!idom[selected_node]){
			DFSU(selected_node);
			parent[label2pre[selected_node]]= label2pre[k];
			dfsparent[selected_node]= k;
		}else{
			arcQueue[last_arcQueue++]= k;
			arcQueue[last_arcQueue++]=selected_node;
		}

		j=Next[j];
	}

	topologicalOrder[topologicalOrderCounter]= k;
	topologicalOrderCounter--;
}

inline void rcompress (int v, int *parent, int *label, int c) {
	int p;

	if((p=parent[v])> c){
		rcompress (p, parent, label, c); //does not change parent[v]
		if (label[p] < label[v]) label[v]= label[p];
		parent[v]= parent[p];
	}
}

// compute dominator tree rooted at s and consisting of vertices in levels >= l
void snca(int s, int l) {
	int i, j, selected_node;

	nextpre= 0;
	if(l < 0) DFSU(s);

	int N= nextpre;
	for(i= 1; i <= N; i++) {
		label[i]= semi[i]= i;
	}

	// process the vertices in reverse preorder
	for (i = N; i > 1; i--) {
		dom[i] = parent[i];
		/*---------------------------------------------
		| check incoming arcs, update semi-dominators
		*--------------------------------------------*/
		int k = pre2label[i];

		j= r_First[k];
		while(j != 0){
			selected_node= r_Target[j];
			int v= label2pre[selected_node]; //v is the source of the arc

			if((v) && (level[selected_node] >= l)){
				int u;

				if(v <= i){
					u= v;//v is an ancestor of i
				}else{
					rcompress(v, parent, label, i);
					u= label[v];
				}

				if(semi[u] < semi[i]){
					semi[i]= semi[u];
					spath[k]= selected_node;
				}
			}

			j = r_Next[j];
		}

		label[i] = semi[i];
	}

	/*-----------------------------------------------------------
	| compute dominators using idom[w]=NCA(I,parent[w],sdom[w])
	*----------------------------------------------------------*/
	dom[1]= 1;
	for(i= 2; i <= N; i++) {
		int j= dom[i];

		while(j> semi[i]){
			j= dom[j];
		}

		dom[i]= j;

		if(l != -1 && idom[pre2label[i]] != pre2label[dom[i]]){
			int tmpLevel= level[idom[pre2label[i]]];
			int tmpNode= idom[pre2label[i]];

			while(tmpLevel != 0){
				size[tmpNode]-= size[pre2label[i]];

				tmpNode= idom[tmpNode];
				tmpLevel--;
			}

			idom[pre2label[i]]= pre2label[dom[i]];
			level[pre2label[i]]= level[pre2label[dom[i]]] + 1;
		}else{
			idom[pre2label[i]]= pre2label[dom[i]];
			level[pre2label[i]]= level[pre2label[dom[i]]] + 1;
		}
	}

	// reset
	for(i= 1; i <= N; i++) {
		int k= pre2label[i];

		label2pre[k]= pre2label[i]= parent[i]= dom[i]= 0;
	}
}

/******************* DELETION ALGORITHM *********************/
// checks if y is still reachable after the deletion of (x,y)
bool isReachable(int y) {
	int j, node_to_visit;
	int support;

	j= r_First[y];
	while(j != 0){
		node_to_visit = r_Target[j];

		if(!idom[node_to_visit]){// node_to_visit is unreachable
			j= r_Next[j];
			continue;
		}

		support= intersectLevel(y, node_to_visit);
		if(support != y) { //fprintf(stdout, "end isReachable %d\n", y);
			return true;
		}

		j = r_Next[j];
	}

	return false;
}

void addToDerivedGraph(int x, int y){
	bool flag= false;
	int tmpPosition= 0, tmpNode= 0;
	int derivedInPosition= derivedGraphCurrentPosition;

	if(derivedOutFirst[x] == 0){
		derivedEdgeCounter[derivedGraphCurrentPosition]++;
		derivedOutTarget[derivedGraphCurrentPosition]= y;
		derivedOutFirst[x]= derivedGraphCurrentPosition;
		derivedOutFirstReverse[derivedGraphCurrentPosition]= x;
		derivedGraphCurrentPosition++;
	}else{
		tmpPosition= derivedOutFirst[x];
		tmpNode= derivedOutTarget[tmpPosition];
		while(flag == false && tmpNode != 0){
			if(tmpNode == y){
				derivedEdgeCounter[tmpPosition]++;
				flag= true; // derived arc (x,y) already exist
			}else{
				tmpPosition= derivedOutNext[tmpPosition];
				tmpNode= derivedOutTarget[tmpPosition];
			}
		}

		if(flag == false){
			derivedEdgeCounter[derivedGraphCurrentPosition]++;
			derivedOutTarget[derivedGraphCurrentPosition]= y;
			derivedOutNext[derivedGraphCurrentPosition]= derivedOutFirst[x];
			derivedOutPrev[derivedOutFirst[x]]= derivedGraphCurrentPosition;
			derivedOutFirstReverse[derivedOutFirst[x]]= 0;
			derivedOutFirst[x]= derivedGraphCurrentPosition;
			derivedOutFirstReverse[derivedGraphCurrentPosition]= x;
			derivedGraphCurrentPosition++;
		}
	}

	if(flag == false && level[x] == level[y] && idom[x] == idom[y]){
		derivedGraphInSiblings[y]++;
	}

	if(flag == false){
		if(derivedInFirst[y] == 0){
			derivedInTarget[derivedInPosition]= x;
			derivedInFirst[y]= derivedInPosition;
			derivedInFirstReverse[derivedInPosition]= y;
		}else{
			tmpPosition= derivedInFirst[y];
			tmpNode= derivedInTarget[tmpPosition];
			while(tmpNode != 0){
				tmpPosition= derivedInNext[tmpPosition];
				tmpNode= derivedInTarget[tmpPosition];
			}

			derivedInTarget[derivedInPosition]= x;
			derivedInNext[derivedInPosition]= derivedInFirst[y];
			derivedInPrev[derivedInFirst[y]]= derivedInPosition;
			derivedInFirstReverse[derivedInFirst[y]]= 0;
			derivedInFirst[y]= derivedInPosition;
			derivedInFirstReverse[derivedInPosition]= y;
		}
	}

	if(x == idom[y]){
		derivedArcFromDominator[y]= true;
	}
}

// -1 -> edge doesn't exist
//  0 -> multiple copies of derived arc
//  1 -> derived arc has been removed
int removeFromDerivedGraph(int x, int y, int mode){
	int tmpPosition= 0;
	int derivedX= 0;
	int derivedY= y;
	int returnValue= 1;
	bool removableArc= false;
	
	violatingLowHighFlag= false;

	if(x == idom[y] || mode == 1){
		derivedX= x;
	}else{
		derivedX= x;

		int counter= level[idom[y]]+1;
		while(prevLevel != counter){
			derivedX= idom[derivedX];
			counter++;
		}
	}

	tmpPosition= derivedOutFirst[derivedX];
	if(derivedOutTarget[tmpPosition] == derivedY){
		if(derivedEdgeCounter[tmpPosition] == 1){
			removableArc= true;
			
			if(derivedOutNext[tmpPosition] != 0) derivedOutPrev[derivedOutNext[tmpPosition]]= 0;
			derivedOutFirstReverse[derivedOutFirst[derivedX]]= 0;
			derivedOutFirst[derivedX]= derivedOutNext[tmpPosition];
			derivedOutFirstReverse[derivedOutNext[tmpPosition]]= derivedX;
			
			derivedGraphCurrentPosition--;
			if(derivedGraphCurrentPosition != tmpPosition){
				derivedEdgeCounter[tmpPosition]= derivedEdgeCounter[derivedGraphCurrentPosition];
				derivedOutTarget[tmpPosition]= derivedOutTarget[derivedGraphCurrentPosition];
				derivedOutNext[tmpPosition]= derivedOutNext[derivedGraphCurrentPosition];
				derivedOutPrev[tmpPosition]= derivedOutPrev[derivedGraphCurrentPosition];
				if(derivedOutPrev[derivedGraphCurrentPosition] != 0) derivedOutNext[derivedOutPrev[derivedGraphCurrentPosition]]= tmpPosition;
				if(derivedOutNext[derivedGraphCurrentPosition] != 0) derivedOutPrev[derivedOutNext[derivedGraphCurrentPosition]]= tmpPosition;
			}

			derivedOutNext[derivedGraphCurrentPosition]= 0;
			derivedOutPrev[derivedGraphCurrentPosition]= 0;
			derivedOutTarget[derivedGraphCurrentPosition]= 0;
			derivedEdgeCounter[derivedGraphCurrentPosition]= 0;

			if(derivedOutFirstReverse[derivedGraphCurrentPosition] != 0){
				derivedOutFirst[derivedOutFirstReverse[derivedGraphCurrentPosition]]= tmpPosition;
				derivedOutFirstReverse[tmpPosition]= derivedOutFirstReverse[derivedGraphCurrentPosition];
				derivedOutFirstReverse[derivedGraphCurrentPosition]= 0;
			}
		}else{
			derivedEdgeCounter[tmpPosition]--;
			returnValue= 0;
		}
	}else{
		while(derivedOutTarget[tmpPosition] != derivedY && derivedOutTarget[tmpPosition] != 0){
			tmpPosition= derivedOutNext[tmpPosition];
		}

		if(derivedOutTarget[tmpPosition] != 0){
			if(derivedEdgeCounter[tmpPosition] == 1){
				removableArc= true;

				if(derivedOutPrev[tmpPosition] != 0) derivedOutNext[derivedOutPrev[tmpPosition]]= derivedOutNext[tmpPosition];
				if(derivedOutNext[tmpPosition] != 0) derivedOutPrev[derivedOutNext[tmpPosition]]= derivedOutPrev[tmpPosition];
				
				derivedGraphCurrentPosition--;
				if(derivedGraphCurrentPosition != tmpPosition){
					derivedEdgeCounter[tmpPosition]= derivedEdgeCounter[derivedGraphCurrentPosition];
					derivedOutTarget[tmpPosition]= derivedOutTarget[derivedGraphCurrentPosition];
					derivedOutNext[tmpPosition]= derivedOutNext[derivedGraphCurrentPosition];
					derivedOutPrev[tmpPosition]= derivedOutPrev[derivedGraphCurrentPosition];
					if(derivedOutPrev[derivedGraphCurrentPosition] != 0) derivedOutNext[derivedOutPrev[derivedGraphCurrentPosition]]= tmpPosition;
					if(derivedOutNext[derivedGraphCurrentPosition] != 0) derivedOutPrev[derivedOutNext[derivedGraphCurrentPosition]]= tmpPosition;
				}

				derivedOutNext[derivedGraphCurrentPosition]= 0;
				derivedOutPrev[derivedGraphCurrentPosition]= 0;
				derivedOutTarget[derivedGraphCurrentPosition]= 0;
				derivedEdgeCounter[derivedGraphCurrentPosition]= 0;

				if(derivedOutFirstReverse[derivedGraphCurrentPosition] != 0){
					derivedOutFirst[derivedOutFirstReverse[derivedGraphCurrentPosition]]= tmpPosition;
					derivedOutFirstReverse[tmpPosition]= derivedOutFirstReverse[derivedGraphCurrentPosition];
					derivedOutFirstReverse[derivedGraphCurrentPosition]= 0;
				}
			}else{
				derivedEdgeCounter[tmpPosition]--;
				returnValue= 0;
			}
		}else{
			returnValue= -1; // doesn't exist
		}
	}

	// updates derivedIn tables if needed
	if(removableArc == true){
		tmpPosition= derivedInFirst[derivedY];

		if(derivedInTarget[tmpPosition] == derivedX){
			if(derivedInNext[tmpPosition] != 0) derivedInPrev[derivedInNext[tmpPosition]]= 0;
			derivedInFirstReverse[derivedInFirst[derivedY]]= 0;
			derivedInFirst[derivedY]= derivedInNext[tmpPosition];
			derivedInFirstReverse[derivedInNext[tmpPosition]]= derivedY;

			if(derivedGraphCurrentPosition != tmpPosition){
				derivedInTarget[tmpPosition]= derivedInTarget[derivedGraphCurrentPosition];
				derivedInNext[tmpPosition]= derivedInNext[derivedGraphCurrentPosition];
				derivedInPrev[tmpPosition]= derivedInPrev[derivedGraphCurrentPosition];
				if(derivedInPrev[derivedGraphCurrentPosition] != 0) derivedInNext[derivedInPrev[derivedGraphCurrentPosition]]= tmpPosition;
				if(derivedInNext[derivedGraphCurrentPosition] != 0) derivedInPrev[derivedInNext[derivedGraphCurrentPosition]]= tmpPosition;
			}

			derivedInNext[derivedGraphCurrentPosition]= 0;
			derivedInPrev[derivedGraphCurrentPosition]= 0;
			derivedInTarget[derivedGraphCurrentPosition]= 0;

			if(derivedInFirstReverse[derivedGraphCurrentPosition] != 0){
				derivedInFirst[derivedInFirstReverse[derivedGraphCurrentPosition]]= tmpPosition;
				derivedInFirstReverse[tmpPosition]= derivedInFirstReverse[derivedGraphCurrentPosition];
				derivedInFirstReverse[derivedGraphCurrentPosition]= 0;
			}
		}else{
			while(derivedInTarget[tmpPosition] != derivedX && derivedInTarget[tmpPosition] != 0){
				tmpPosition= derivedInNext[tmpPosition];
			}

			if(derivedInTarget[tmpPosition] != 0){
				if(derivedInPrev[tmpPosition] != 0) derivedInNext[derivedInPrev[tmpPosition]]= derivedInNext[tmpPosition];
				if(derivedInNext[tmpPosition] != 0) derivedInPrev[derivedInNext[tmpPosition]]= derivedInPrev[tmpPosition];

				if(derivedGraphCurrentPosition != tmpPosition){
					derivedInTarget[tmpPosition]= derivedInTarget[derivedGraphCurrentPosition];
					derivedInNext[tmpPosition]= derivedInNext[derivedGraphCurrentPosition];
					derivedInPrev[tmpPosition]= derivedInPrev[derivedGraphCurrentPosition];
					if(derivedInPrev[derivedGraphCurrentPosition] != 0) derivedInNext[derivedInPrev[derivedGraphCurrentPosition]]= tmpPosition;
					if(derivedInNext[derivedGraphCurrentPosition] != 0) derivedInPrev[derivedInNext[derivedGraphCurrentPosition]]= tmpPosition;
				}

				derivedInNext[derivedGraphCurrentPosition]= 0;
				derivedInPrev[derivedGraphCurrentPosition]= 0;
				derivedInTarget[derivedGraphCurrentPosition]= 0;

				if(derivedInFirstReverse[derivedGraphCurrentPosition] != 0){
					derivedInFirst[derivedInFirstReverse[derivedGraphCurrentPosition]]= tmpPosition;
					derivedInFirstReverse[tmpPosition]= derivedInFirstReverse[derivedGraphCurrentPosition];
					derivedInFirstReverse[derivedGraphCurrentPosition]= 0;
				}
			}
		}
	}

	if(derivedX == idom[derivedY]){
		derivedArcFromDominator[y]= false;
		violatingLowHighFlag= true;
	}else if(derivedInLowHigh[derivedY][0] == derivedX || derivedInLowHigh[derivedY][1] == derivedX){
		violatingLowHighFlag= true;
	}

	return(returnValue);
}

void addToQList(int node){
	bool flag= false;
	int tmpPosition= r_First[node];
	int tmpNode= r_Target[tmpPosition];

	while(flag == false && tmpNode != 0){
		if(idom[node] == tmpNode){
			flag= true;
		}else{
			tmpPosition= r_Next[tmpPosition];
			tmpNode= r_Target[tmpPosition];
		}
	}

	if(flag == false && inQList[node] == 0){
		QList[nodesInQList]= node;
		inQList[node]= 1;
		nodesInQList++;
	}
}

void checkIncomingEdges(int node){
	int tmpPosition= r_First[node];
	int incomingEdge= r_Target[tmpPosition];
	int derivedX= 0;

	while(incomingEdge != 0){
		if(incomingEdge == idom[node]){
			derivedX= incomingEdge;

			int tmpNode= incomingEdge;
			while(level[tmpNode] != prevLevel){
				tmpNode= idom[tmpNode];
			}

			if(tmpNode != derivedX){
				if(removeFromDerivedGraph(tmpNode, node, 1)){	
					derivedGraphInSiblings[node]--;
				}

				addToDerivedGraph(derivedX, node);
			}else{
				if(prevLevel == level[tmpNode]){
					derivedGraphInSiblings[node]--;
				}
			}
		}else{
			derivedX= incomingEdge;

			while(level[derivedX] != 1 && level[derivedX] != level[node]){
				derivedX= idom[derivedX];
			}

			int tmpNode= incomingEdge;
			while(level[tmpNode] != prevLevel){
				tmpNode= idom[tmpNode];
			}

			int value= removeFromDerivedGraph(tmpNode, node, 1);
			if(value != -1){
				if(value == 1) derivedGraphInSiblings[node]--;
				addToDerivedGraph(derivedX, node);
			}
		}

		tmpPosition= r_Next[tmpPosition];
		incomingEdge= r_Target[tmpPosition];
	}
}

void addToViolatingLowHigh(int node){
	if(inViolatingLowHigh[node] == false){
		violatingLowHigh[violatingLowHighCounter]= node;
		positionInViolatingLowHigh[node]= violatingLowHighCounter;
		violatingLowHighCounter++;
		inViolatingLowHigh[node]= true;
	}
}

void addToNeedUpdateLowHigh(int node){
	inLowHighOrder[node]= false;

	if(inNeedUpdateLowHigh[node] == false){
		needUpdateLowHigh[needUpdateLowHighCounter]= node;
		inNeedUpdateLowHigh[node]= true;
		needUpdateLowHighCounter++;
	}
}

void updateLowHighIds(int node, int idomNode){
	int left= lowHighPrevNode[node];
	int right= lowHighNextNode[node];
	unsigned long long int minId= lowHighId[left];
	unsigned long long int maxId= lowHighId[right];
	int counter= 3; // left, node, right
	int level= 1;
	unsigned long int idsBetweenNodes= 0;
	unsigned long int nextId= 0;
	double overflowThreshold= 1/T;
	double density= 0.0;
	bool limitsFlag= false;

	if(left == 0) left= right;
	density= (double)((double)counter)/(maxId-minId+1);

	while(overflowThreshold <= density && limitsFlag == false){
		level++;

		if(minId != 0 && (minId%(1L << level) != 0)){
			minId= minId-(minId%(1L << level));
		}

		if(maxId <= ULLONG_MAX/4 && (maxId%(1L << level) != (unsigned)((1LL << level)-1))){
			maxId= minId+(1L << level)-1;
		}

		if(maxId >= ULLONG_MAX/4) limitsFlag= true;

		while(lowHighPrevNode[left] != 0 && lowHighId[lowHighPrevNode[left]] >= minId){
			left= lowHighPrevNode[left];
			counter++;
		}

		while(lowHighNextNode[right] != 0 && lowHighId[lowHighNextNode[right]] <= maxId){
			right= lowHighNextNode[right];
			counter++;
		}

		density= (double)((double)counter)/(maxId-minId+1);
		overflowThreshold= overflowThreshold/T;
	}

	if(minId == 0){
		minId++;
		left= lowHighHead[idomNode];
	}else{
		if(lowHighId[left] < minId)left= lowHighNextNode[left];
	}

	lowHighId[left]= minId;
	idsBetweenNodes= (unsigned long int)(1/density);
	nextId= minId+idsBetweenNodes;
	left= lowHighNextNode[left];

	while(left != right){
		lowHighId[left]= nextId;
		nextId+= idsBetweenNodes;
		left= lowHighNextNode[left];
	}

	if(lowHighId[right] < maxId) lowHighId[right]= nextId;
}

void giveNodeLowHighId(int node, int left, int right){
	if(!(left == 0 && right == 0) && lowHighId[right]-lowHighId[left] == 1){
		updateLowHighIds(node, idom[node]);
	}else if(left == 0 && right == 0){
		lowHighId[node]= ULLONG_MAX/4;
	}else if(left == 0){
		lowHighId[node]= lowHighId[right]/2;	
	}else{
		lowHighId[node]= lowHighId[left]+(lowHighId[right]-lowHighId[left])/2;
	}
}

void addToDerivedOutLowHigh(int node, int parent){
	if(derivedOutLowHighFirst[parent] == 0){
		derivedOutLowHighTarget[derivedOutLowHighCurrentPosition]= node;
		derivedOutLowHighFirst[parent]= derivedOutLowHighCurrentPosition;
		derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]= parent;
		derivedOutLowHighCurrentPosition++;
	}else{
		derivedOutLowHighTarget[derivedOutLowHighCurrentPosition]= node;
		derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]= 0;
		derivedOutLowHighNext[derivedOutLowHighCurrentPosition]= derivedOutLowHighFirst[parent];
		derivedOutLowHighPrev[derivedOutLowHighFirst[parent]]= derivedOutLowHighCurrentPosition;
		
		
		derivedOutLowHighFirstReverse[derivedOutLowHighFirst[parent]]= 0;
		derivedOutLowHighFirst[parent]= derivedOutLowHighCurrentPosition;
		derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]= parent;
		derivedOutLowHighCurrentPosition++;
	}
}

void addChildToLowHigh(int node, int idomNode){
	int derivedArc1= 0, derivedArc2= 0;
	bool derivedArcFromIdom= false;
	int tmpPosition= derivedInFirst[node];
	int tmpNode= derivedInTarget[tmpPosition];

	inLowHighChildrenList[node]= true;
	while(derivedArc2 == 0 && derivedArcFromIdom == false){
		if(tmpNode == idomNode){
			derivedArcFromDominator[node]= true;
			derivedArcFromIdom= true;
		}else if(inLowHighOrder[tmpNode] == true){
			if(derivedArc1 == 0){
				derivedArc1= tmpNode;
			}else{
				derivedArc2= tmpNode;
			}
		}
				
		tmpPosition= derivedInNext[tmpPosition];
		tmpNode= derivedInTarget[tmpPosition];
	}

	if(derivedArcFromIdom == true){
		if(lowHighHead[idomNode] == 0){
			lowHighHead[idomNode]= node;
			giveNodeLowHighId(node, 0, 0);
		}else{
			lowHighPrevNode[lowHighHead[idomNode]]= node;
			lowHighNextNode[node]= lowHighHead[idomNode];
			lowHighHead[idomNode]= node;
			giveNodeLowHighId(node, 0, lowHighNextNode[node]);
		}

		derivedInLowHigh[node][0]= idom[node];
		derivedInLowHigh[node][1]= idom[node];
	}else{
		int left= 0;
		int right= 0;
		
		if(lowHighId[derivedArc1] < lowHighId[derivedArc2]){
			left= derivedArc1;
		}else{
			left= derivedArc2;
		}
		right= lowHighNextNode[left];
		
		lowHighNextNode[left]= node;
		lowHighPrevNode[node]= left;

		lowHighPrevNode[right]= node;
		lowHighNextNode[node]= right;

		giveNodeLowHighId(node, left, right);

		addToDerivedOutLowHigh(node, derivedArc1);
		derivedInLowHigh[node][0]= derivedArc1;
		derivedInLowHighReversePosition[node][0]= derivedOutLowHighCurrentPosition-1;
		derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= node;

		addToDerivedOutLowHigh(node, derivedArc2);
		derivedInLowHigh[node][1]= derivedArc2;
		derivedInLowHighReversePosition[node][1]= derivedOutLowHighCurrentPosition-1;
		derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= node;
	}
}

void removeFromDerivedOutLowHigh(int node, int parent){
	int tmpPosition= 0;

	if(derivedInLowHigh[node][0] == parent){
		tmpPosition= derivedInLowHighReversePosition[node][0];
	}else{
		tmpPosition= derivedInLowHighReversePosition[node][1];
	}

	if(derivedOutLowHighTarget[derivedOutLowHighFirst[parent]] == node){
		if(derivedOutLowHighNext[tmpPosition] != 0) derivedOutLowHighPrev[derivedOutLowHighNext[tmpPosition]]= 0;
		derivedOutLowHighFirstReverse[derivedOutLowHighFirst[parent]]= 0;
		derivedOutLowHighFirst[parent]= derivedOutLowHighNext[tmpPosition];
		derivedOutLowHighFirstReverse[derivedOutLowHighNext[tmpPosition]]= parent;

		derivedOutLowHighCurrentPosition--;
		if(derivedOutLowHighCurrentPosition != tmpPosition){
			derivedOutLowHighTarget[tmpPosition]= derivedOutLowHighTarget[derivedOutLowHighCurrentPosition];
			derivedOutLowHighNext[tmpPosition]= derivedOutLowHighNext[derivedOutLowHighCurrentPosition];
			derivedOutLowHighPrev[tmpPosition]= derivedOutLowHighPrev[derivedOutLowHighCurrentPosition];

			if(derivedOutLowHighPrev[derivedOutLowHighCurrentPosition] != 0) derivedOutLowHighNext[derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]]= tmpPosition;
			if(derivedOutLowHighNext[derivedOutLowHighCurrentPosition] != 0) derivedOutLowHighPrev[derivedOutLowHighNext[derivedOutLowHighCurrentPosition]]= tmpPosition;
		}

		int tmp= derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition];
		if(derivedInLowHighReversePosition[tmp][0] == derivedOutLowHighCurrentPosition){
			derivedInLowHighReversePosition[tmp][0]= tmpPosition;
			derivedInLowHighReverseNode[tmpPosition]= tmp;
		}else if(derivedInLowHighReversePosition[tmp][1] == derivedOutLowHighCurrentPosition){
			derivedInLowHighReversePosition[tmp][1]= tmpPosition;
			derivedInLowHighReverseNode[tmpPosition]= tmp;
		}

		if(derivedInLowHigh[node][0] == parent){
			derivedInLowHigh[node][0]= 0;
			derivedInLowHighReversePosition[node][0]= 0;
		}else{
			derivedInLowHigh[node][1]= 0;
			derivedInLowHighReversePosition[node][1]= 0;
		}		

		derivedOutLowHighNext[derivedOutLowHighCurrentPosition]= 0;
		derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]= 0;
		derivedOutLowHighTarget[derivedOutLowHighCurrentPosition]= 0;

		if(derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition] != 0){
			derivedOutLowHighFirst[derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]]= tmpPosition;
			derivedOutLowHighFirstReverse[tmpPosition]= derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition];
			derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]= 0;
		}
	}else{
		if(derivedOutLowHighTarget[tmpPosition] != 0){
			if(derivedOutLowHighPrev[tmpPosition] != 0) derivedOutLowHighNext[derivedOutLowHighPrev[tmpPosition]]= derivedOutLowHighNext[tmpPosition];
			if(derivedOutLowHighNext[tmpPosition] != 0) derivedOutLowHighPrev[derivedOutLowHighNext[tmpPosition]]= derivedOutLowHighPrev[tmpPosition];

			derivedOutLowHighCurrentPosition--;
			if(derivedOutLowHighCurrentPosition != tmpPosition){
				derivedOutLowHighTarget[tmpPosition]= derivedOutLowHighTarget[derivedOutLowHighCurrentPosition];
				derivedOutLowHighNext[tmpPosition]= derivedOutLowHighNext[derivedOutLowHighCurrentPosition];
				derivedOutLowHighPrev[tmpPosition]= derivedOutLowHighPrev[derivedOutLowHighCurrentPosition];

				if(derivedOutLowHighPrev[derivedOutLowHighCurrentPosition] != 0) derivedOutLowHighNext[derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]]= tmpPosition;
				if(derivedOutLowHighNext[derivedOutLowHighCurrentPosition] != 0) derivedOutLowHighPrev[derivedOutLowHighNext[derivedOutLowHighCurrentPosition]]= tmpPosition;
			}

			int tmp= derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition];
			if(derivedInLowHighReversePosition[tmp][0] == derivedOutLowHighCurrentPosition){
				derivedInLowHighReversePosition[tmp][0]= tmpPosition;
				derivedInLowHighReverseNode[tmpPosition]= tmp;
			}else if(derivedInLowHighReversePosition[tmp][1] == derivedOutLowHighCurrentPosition){
				derivedInLowHighReversePosition[tmp][1]= tmpPosition;
				derivedInLowHighReverseNode[tmpPosition]= tmp;
			}

			if(derivedInLowHigh[node][0] == parent){
				derivedInLowHigh[node][0]= 0;
				derivedInLowHighReversePosition[node][0]= 0;
			}else{
				derivedInLowHigh[node][1]= 0;
				derivedInLowHighReversePosition[node][1]= 0;
			}		

			derivedOutLowHighNext[derivedOutLowHighCurrentPosition]= 0;
			derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]= 0;
			derivedOutLowHighTarget[derivedOutLowHighCurrentPosition]= 0;

			if(derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition] != 0){
				derivedOutLowHighFirst[derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]]= tmpPosition;
				derivedOutLowHighFirstReverse[tmpPosition]= derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition];
				derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]= 0;
			}
		}
	}
}

bool removeChildFromLowHigh(int node, int idomNode){
	int leftNode= lowHighPrevNode[node];
	int rightNode= lowHighNextNode[node];
	bool returnValue= false;

	if(inLowHighChildrenList[node] == true){
		if(leftNode != 0){
			lowHighNextNode[leftNode]= lowHighNextNode[node];
		}else{
			lowHighHead[idomNode]= lowHighNextNode[node];
		}

		if(rightNode != 0){
			lowHighPrevNode[rightNode]= lowHighPrevNode[node];
		}

		lowHighPrevNode[node]= 0;
		lowHighNextNode[node]= 0;

		if(derivedInLowHigh[node][0] != derivedInLowHigh[node][1]){
			removeFromDerivedOutLowHigh(node, derivedInLowHigh[node][0]);
			removeFromDerivedOutLowHigh(node, derivedInLowHigh[node][1]);
		}

		derivedArcFromDominator[node]= false;
		inLowHighChildrenList[node]= false;

		returnValue= true;
	}

	return(returnValue);
}

void removeFromViolatingLowHigh(int node){
	int position= positionInViolatingLowHigh[node];
	int lastInViolatingLowHigh= violatingLowHigh[violatingLowHighCounter-1];

	violatingLowHigh[position]= lastInViolatingLowHigh;	
	positionInViolatingLowHigh[lastInViolatingLowHigh]= position;
	violatingLowHigh[violatingLowHighCounter-1]= 0;
	violatingLowHighCounter--;
	positionInViolatingLowHigh[node]= 0;
	inViolatingLowHigh[node]= false;
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
void updateInSiblings(int w, int c, int lowHighDominator, int mode){
	int qPosition= derivedOutFirst[w];
	int q= derivedOutTarget[qPosition];
	int prevQPosition= qPosition;
	bool qBelongsDerivedOutC= false;

	qPosition= derivedOutFirst[w];
	q= derivedOutTarget[qPosition];
	while(q != 0){
		int tmpDerivedOutPositionC= derivedOutFirst[c];
		int tmpDerivedOutC= derivedOutTarget[tmpDerivedOutPositionC];
		
		qBelongsDerivedOutC= false;
		while(qBelongsDerivedOutC == false && tmpDerivedOutC != 0){
			if(tmpDerivedOutC == q){
				qBelongsDerivedOutC= true;
			}else{
				tmpDerivedOutPositionC= derivedOutNext[tmpDerivedOutPositionC];
				tmpDerivedOutC= derivedOutTarget[tmpDerivedOutPositionC];
			}
		}
		prevQPosition= qPosition;
		qPosition= derivedOutNext[qPosition];

		if(qBelongsDerivedOutC == true){
			derivedGraphInSiblings[q]--;
			if(derivedGraphInSiblings[q] == 1){
				addToQList(q);

				if(inViolatingLowHigh[q] == true && inQList[q] == 1){
					removeFromViolatingLowHigh(q);
				}else if((derivedInLowHigh[q][0] == w || derivedInLowHigh[q][1] == w) && idom[q] == lowHighDominator){
					addToViolatingLowHigh(q);
				}
			}else{
				if((derivedInLowHigh[q][0] == w || derivedInLowHigh[q][1] == w) && idom[q] == lowHighDominator){
					addToViolatingLowHigh(q);
				}
			}

			while(!(removeFromDerivedGraph(w, q, 0))){
				if(qPosition == derivedGraphCurrentPosition){
					qPosition= prevQPosition;
				}
				addToDerivedGraph(c, q);
			}
			if(qPosition == derivedGraphCurrentPosition){
				qPosition= prevQPosition;
			}
			addToDerivedGraph(c, q);
		}else{
			if(prevLevel == level[q]){
				derivedGraphInSiblings[q]--;

				while(!(removeFromDerivedGraph(w, q, 0))){
					if(qPosition == derivedGraphCurrentPosition){
						qPosition= prevQPosition;
					}

					addToDerivedGraph(c, q);
				}

				if(qPosition == derivedGraphCurrentPosition){
					qPosition= prevQPosition;
				}
				addToDerivedGraph(c, q);
			}

			if((derivedInLowHigh[q][0] == w || derivedInLowHigh[q][1] == w) && idom[q] == lowHighDominator){
				addToViolatingLowHigh(q);
			}
		}
			
		q= derivedOutTarget[qPosition];
	}

	if(mode == 0){
		bool removeChildFromLowHighFlag= removeChildFromLowHigh(w, prevIdom[w]);
		if(removeChildFromLowHighFlag == true) addChildToLowHigh(w, idom[w]);
		inLowHighOrder[w]= true;
	}

	prevIdom[w]= idom[w];
}

void dfsDominator(int node){
	int position, selectedNode;

	dfsDominatorDiscovered[node]= 1;
	createPreorderList(node);
	preorder2labelDominator[node]= dfsDominatorCounter;
	label2preorderDominator[dfsDominatorCounter++]= node;

	position= dominatorFirst[node];
	while(position != 0){
		selectedNode= dominatorTarget[position];

		if(dfsDominatorDiscovered[selectedNode] == 1){
			position= dominatorNext[position];
			continue;
		}else{
			dfsDominator(selectedNode);
			createPostorderList(selectedNode);
			size[node]+= size[selectedNode];
		}
	}

	if(node == r) createPostorderList(node);
}

void initializeDominatorTreeStructures(){
	int nodes= n+1;
	int currentPosition= 1;

	// calculate dominator tree from idom's
	for(int i= 1; i <= nodes; i++){
		if(idom[i] != i && idom[i] != 0){ // except the root of dominator tree and unreachable nodes
			if(dominatorFirst[idom[i]] == 0){
				dominatorTarget[currentPosition]= i;
				dominatorFirst[idom[i]]= currentPosition++;
			}else{
				dominatorTarget[currentPosition]= i;
				dominatorNext[currentPosition]= dominatorFirst[idom[i]];
				dominatorFirst[idom[i]]= currentPosition++;
			}
		}
	}

	dfsDominator(r);
}

void initializeDerivedGraphStructures(){
	derivedGraphCurrentPosition= 1;

	for(int i= 0; i < n+1; i++){
		derivedOutFirst[i]= 0;
		derivedInFirst[i]= 0;
		derivedGraphInSiblings[i]= 0;
	}

	for(int i= 0; i < m+1; i++){
		derivedOutNext[i]= 0;
		derivedOutPrev[i]= 0;
		derivedOutTarget[i]= 0;
		derivedInNext[i]= 0;
		derivedInPrev[i]= 0;
		derivedInTarget[i]= 0;
		derivedEdgeCounter[i]= 0;
		derivedOutFirstReverse[i]= 0;
	}
}

inline bool isChild(int parent, int child){
	if(parent == child){
		return(true);
	}

	if(nodesTablePreorder[parent]->rep->tag > nodesTablePreorder[child]->rep->tag){
		return (false);
	}else if(nodesTablePostorder[parent]->rep->tag < nodesTablePostorder[child]->rep->tag){
		return (false);
	}else if(nodesTablePreorder[parent]->rep->tag == nodesTablePreorder[child]->rep->tag && nodesTablePreorder[parent]->tag >= nodesTablePreorder[child]->tag){
		return (false);
	}else if(nodesTablePostorder[parent]->rep->tag == nodesTablePostorder[child]->rep->tag && nodesTablePostorder[parent]->tag <= nodesTablePostorder[child]->tag){
		return (false);
	}

	return(true);
}

void relabelRepresentatives(int node, int mode, int totalRepresentatives){
	struct representative* left= NULL;
	struct representative* right= NULL;
	struct representative* stoppingPoint= NULL;
	int counter= 1;
	int level= 1;
	unsigned long int minId= 0;
	unsigned long int maxId= 0;
	unsigned long int idsBetweenRepresentatives= 0;
	unsigned long int nextId= 0;
	double overflowThreshold= 1/T;
	double density= 0.0;

	if(mode == 0){ // preorder
		left= nodesTablePreorder[node]->rep;
		right= left->rightRepresentative;
		minId= left->tag;
		(right != NULL) ? maxId= right->tag : maxId= ULLONG_MAX/4;

		if(right != NULL) counter++;
		density= (double)((double)counter + (double)totalRepresentatives)/(maxId-minId+1);

		while(overflowThreshold <= density){
			level++;

			if(minId != 0 && (minId%(1L << level) != 0)){
				minId= minId-(minId%(1L << level));
			}

			if(maxId != ULLONG_MAX/4 && (maxId%(1L << level) != (unsigned)((1LL << level)-1))){
				maxId= minId+(1L << level)-1;
			}

			while(left->leftRepresentative != NULL && left->leftRepresentative->tag >= minId){
				left= left->leftRepresentative;
				counter++;
			}

			while(right != NULL && right->rightRepresentative != NULL && right->rightRepresentative->tag <= maxId){
				right= right->rightRepresentative;
				counter++;
			}

			density= (double)((double)counter + (double)totalRepresentatives)/(maxId-minId+1);
			overflowThreshold= overflowThreshold/T;
		}

		left->tag= minId;
		idsBetweenRepresentatives= (unsigned long int)(1/density);

		if(left == nodesTablePreorder[node]->rep){
			nextId= minId+((totalRepresentatives+1)*idsBetweenRepresentatives);
		}else{
			nextId= minId+idsBetweenRepresentatives;
		}

		left= left->rightRepresentative;

		(right == NULL) ? stoppingPoint= NULL : stoppingPoint= right->rightRepresentative;

		while(left != stoppingPoint){
			left->tag= nextId;

			if(left == nodesTablePreorder[node]->rep){
				nextId= nextId+((totalRepresentatives+1)*idsBetweenRepresentatives);
			}else{
				nextId= nextId+idsBetweenRepresentatives;
			}

			left= left->rightRepresentative;
		}
	}else{ // postorder
		right= nodesTablePostorder[node]->rep;
		left= right->leftRepresentative;
		(left != NULL) ? minId= left->tag : minId= 0;
		maxId= right->tag;

		if(left != NULL) counter++;
		density= (double)((double)counter + (double)totalRepresentatives)/(maxId-minId+1);

		while(overflowThreshold <= density){
			level++;

			if(minId != 0 && (minId%(1L << level) != 0)){
				minId= minId-(minId%(1L << level));
			}

			if(maxId != ULLONG_MAX/4 && (maxId%(1L << level) != (unsigned)((1LL << level)-1))){
				maxId= minId+(1L << level)-1;
			}

			while(left != NULL && left->leftRepresentative != NULL && left->leftRepresentative->tag >= minId){
				left= left->leftRepresentative;
				counter++;
			}

			while(right->rightRepresentative != NULL && right->rightRepresentative->tag <= maxId){
				right= right->rightRepresentative;
				counter++;
			}

			density= (double)((double)counter + (double)totalRepresentatives)/(maxId-minId+1);
			overflowThreshold= overflowThreshold/T;
		}

		right->tag= maxId;
		idsBetweenRepresentatives= (unsigned long int)(1/density);

		if(right == nodesTablePostorder[node]->rep){
			nextId= maxId-((totalRepresentatives+1)*idsBetweenRepresentatives);
		}else{
			nextId= maxId-idsBetweenRepresentatives;
		}

		right= right->leftRepresentative;
		(left == NULL) ? stoppingPoint= NULL : stoppingPoint= left->leftRepresentative;

		while(right != stoppingPoint){
			right->tag= nextId;

			if(right == nodesTablePostorder[node]->rep){
				nextId= nextId-((totalRepresentatives+1)*idsBetweenRepresentatives);
			}else{
				nextId= nextId-idsBetweenRepresentatives;
			}

			right= right->leftRepresentative;
		}
	}
}

// mode == 0 -> preorder
// mode == 1 -> postorder
void splitRepresentative(struct node* left, struct node* right, int mode){
	struct node* tmpNode= NULL;
	struct representative* newRep= NULL;
	struct representative* leftRep= left->rep;
	struct representative* rightRep= left->rep->rightRepresentative;
	unsigned long int idDifference= 0;
	int counter= 0;
	int totalLeaves= left->rep->leaves;

	newRep= createNewRepresentative(right->nodesName);
	if(leftRep == representativesListTailPostorder){
		representativesListTailPostorder= newRep;
	}

	if(rightRep == NULL){
		idDifference= ULLONG_MAX/4 - leftRep->tag;
	}else{
		idDifference= rightRep->tag - leftRep->tag;
	}

	if(idDifference == 1){
		if(mode == 0){
			relabelRepresentatives(left->nodesName, 0, 1);
		}else{
			relabelRepresentatives(right->nodesName, 1, 1);
		}

		if(rightRep == NULL){
			idDifference= ULLONG_MAX/4 - leftRep->tag;
		}else{
			idDifference= rightRep->tag - leftRep->tag;
		}
	}
	newRep->tag= leftRep->tag + (idDifference/2);

	newRep->leftRepresentative= left->rep;
	newRep->rightRepresentative= left->rep->rightRepresentative;
	left->rep->rightRepresentative= newRep;
	if(newRep->rightRepresentative != NULL) newRep->rightRepresentative->leftRepresentative= newRep;
	newRep->nodesListHead= right;
	newRep->nodesListTail= left->rep->nodesListTail;
	right->rep= newRep;
	right->leftNode= NULL;
	left->rightNode= NULL;
	left->rep->nodesListTail= left;

	for(tmpNode= left->rep->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode){
		counter++;
	}

	newRep->leaves= left->rep->leaves-counter;
	left->rep->leaves= counter;

	tmpNode= left->rep->nodesListHead;
	tmpNode->tag= 0;
	tmpNode= tmpNode->rightNode;

	while(tmpNode != NULL){
		tmpNode->tag= tmpNode->leftNode->tag+(1LL << (nodesPerRepresentative-left->rep->leaves));
		tmpNode= tmpNode->rightNode;
	}

	tmpNode= newRep->nodesListHead;
	tmpNode->tag= 0;
	tmpNode->rep= newRep;
	tmpNode= tmpNode->rightNode;

	while(tmpNode != NULL){
		tmpNode->tag= tmpNode->leftNode->tag + (1LL << (nodesPerRepresentative-newRep->leaves));
		tmpNode->rep= newRep;
		tmpNode= tmpNode->rightNode;
	}
}

// 0 -> preorder
// 1 -> postorder
void cutMovingNodes(struct node* left, struct node* right, struct node* movingLeft, struct node* movingRight, int mode){
	struct representative* leftRepresentative= NULL;
	struct representative* rightRepresentative= NULL;

	if(mode == 0){ // preorder
		if(left->rep == movingLeft->rep) splitRepresentative(left, movingLeft, 0);
		if(right != NULL && right->rep == movingRight->rep) splitRepresentative(movingRight, right, 0);

		leftRepresentative= left->rep;
		if(right != NULL) rightRepresentative= right->rep;

		if(right != NULL){	
			if(leftRepresentative != rightRepresentative){
				leftRepresentative->rightRepresentative->leftRepresentative= NULL;
				rightRepresentative->leftRepresentative->rightRepresentative= NULL;
				leftRepresentative->rightRepresentative= rightRepresentative;
				rightRepresentative->leftRepresentative= leftRepresentative;
			}
		}else{
			leftRepresentative->rightRepresentative->leftRepresentative= NULL;
			leftRepresentative->rightRepresentative=  NULL;
		}
	}else{ //postorder
		if(left != NULL && left->rep == movingLeft->rep)	 splitRepresentative(left, movingLeft, 1);
		if(right->rep == movingRight->rep) splitRepresentative(movingRight, right, 1);

		if(left != NULL) leftRepresentative= left->rep;
		rightRepresentative= right->rep;

		if(left != NULL){
			if(leftRepresentative != rightRepresentative){
				leftRepresentative->rightRepresentative->leftRepresentative= NULL;
				rightRepresentative->leftRepresentative->rightRepresentative= NULL;
				leftRepresentative->rightRepresentative= rightRepresentative;
				rightRepresentative->leftRepresentative= leftRepresentative;
			}
		}else{
			rightRepresentative->leftRepresentative->rightRepresentative= NULL;
			rightRepresentative->leftRepresentative= NULL;
		}
	}
}

void mergeRepresentatives(struct representative* leftRep, struct representative* rightRep){
	leftRep->nodesListTail->rightNode= rightRep->nodesListHead;
	rightRep->nodesListHead->leftNode= leftRep->nodesListTail;

	leftRep->leaves= leftRep->leaves+rightRep->leaves;
	leftRep->tag= leftRep->tag+((rightRep->tag-leftRep->tag)/2);
	leftRep->rightRepresentative= rightRep->rightRepresentative;
	leftRep->nodesListTail= rightRep->nodesListTail;
	if(rightRep->rightRepresentative != NULL) rightRep->rightRepresentative->leftRepresentative= leftRep;

	struct node* currentNode= leftRep->nodesListHead;
	currentNode->tag= 0;
	currentNode= currentNode->rightNode;
	currentNode->rep= leftRep;

	while(currentNode != NULL){
		currentNode->tag= currentNode->leftNode->tag+(1LL << (nodesPerRepresentative-leftRep->leaves));
		currentNode->rep= leftRep;

		currentNode= currentNode->rightNode;
	}

	if(rightRep == representativesListTailPostorder) representativesListTailPostorder= leftRep;
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
void updateIds(int x, int y, int mode){ // y is the new idom of x (idom[x] == y)
	struct node* leftNodePreorder= NULL; // aristeros komvos apo tous komvous pou tha metakinithoun
	struct node* rightNodePreorder= NULL; // dexios komvos apo tous komvous pou tha metakinithoun
	struct node* movingNodeLeftPreorder= NULL; // aristeroteros komvos apo autous pou tha metakinithoun
	struct node* movingNodeRightPreorder= NULL; // dexios komvos apo autous pou tha metakinithoun
	struct node* newNodeLeftPreorder= NULL;
	struct node* newNodeRightPreorder= NULL;

	struct representative* leftRepresentativePreorder= NULL; // aristeros antiproswpos apo tous komvous pou tha metakinithoun
	struct representative* rightRepresentativePreorder= NULL; // dexios antiproswpos apo tous komvous pou tha metakinithoun
	struct representative* movingRepresentativeLeftPreorder= NULL; // aristeroteros antiproswpos apo autous pou tha metakinithoun
	struct representative* movingRepresentativeRightPreorder= NULL; // dexios antiproswpos apo autous pou tha metakinithoun
	struct representative* newRepresentativeLeftPreorder= NULL; // aristeroteros antiproswpos ths neas theshs twn komvwn
	struct representative* newRepresentativeRightPreorder= NULL; // dexios antiproswpos ths neas theshs twn komvwn

	struct node* leftNodePostorder= NULL;
	struct node* rightNodePostorder= NULL;
	struct node* movingNodeLeftPostorder= NULL;
	struct node* movingNodeRightPostorder= NULL;
	struct node* newNodeLeftPostorder= NULL;
	struct node* newNodeRightPostorder= NULL;

	struct representative* leftRepresentativePostorder= NULL;
	struct representative* rightRepresentativePostorder= NULL;
	struct representative* movingRepresentativeLeftPostorder= NULL;
	struct representative* movingRepresentativeRightPostorder= NULL;
	struct representative* newRepresentativeLeftPostorder= NULL;
	struct representative* newRepresentativeRightPostorder= NULL;

	struct representative* tmpRepresentative= NULL;	
	struct node* tmpNode= NULL;

	unsigned long int representativesCounterPreorder= 0;
	unsigned long int representativesCounterPostorder= 0;
	unsigned long int idDifferencePreorder= 0;
	unsigned long int idDifferencePostorder= 0;
	unsigned long int idsBetweenNodes= 0;
	unsigned long int nextId= 0;

	bool preorderFlag= false;
	bool postorderFlag= false;

	if(y == -1){ // node x became unreachable
		// preorder
		leftNodePreorder= nodesTablePreorder[x]->leftNode;

		if(leftNodePreorder == NULL){
			leftNodePreorder= nodesTablePreorder[x]->rep->leftRepresentative->nodesListTail;
			// we can always move left cause root is the first node in preorder list
		}

		rightNodePreorder= nodesTablePreorder[x]->rightNode;
		if(rightNodePreorder == NULL && nodesTablePreorder[x]->rep->rightRepresentative != NULL){
			rightNodePreorder= nodesTablePreorder[x]->rep->rightRepresentative->nodesListHead;
		}
		(rightNodePreorder != NULL) ? rightRepresentativePreorder= rightNodePreorder->rep : rightRepresentativePreorder= nodesTablePreorder[x]->rep;
		
		while(rightNodePreorder != NULL && level[rightNodePreorder->nodesName] > prevLevel && rightRepresentativePreorder->rightRepresentative != NULL){
			if(isChild(x, rightRepresentativePreorder->rightRepresentative->representativesName)){
				rightRepresentativePreorder= rightRepresentativePreorder->rightRepresentative;
				rightNodePreorder= rightRepresentativePreorder->nodesListHead;
			}else{
				break;
			}
		}

		if(rightNodePreorder != NULL && rightNodePreorder->rep != rightRepresentativePreorder) rightNodePreorder= rightRepresentativePreorder->nodesListHead;
		while(rightNodePreorder != NULL && level[rightNodePreorder->nodesName] > prevLevel) rightNodePreorder= rightNodePreorder->rightNode;

		if(rightNodePreorder == NULL && rightRepresentativePreorder->rightRepresentative != NULL){
			rightRepresentativePreorder= rightRepresentativePreorder->rightRepresentative;
			rightNodePreorder= rightRepresentativePreorder->nodesListHead;
		}else if(rightNodePreorder == NULL && rightRepresentativePreorder->rightRepresentative == NULL){
			rightRepresentativePreorder= NULL;
		}
		
		leftRepresentativePreorder= leftNodePreorder->rep;
		(rightNodePreorder != NULL) ? rightRepresentativePreorder= rightNodePreorder->rep : rightRepresentativePreorder= NULL;

		struct node* tmpNode= leftNodePreorder->rightNode;
		if(tmpNode == NULL) tmpNode= leftNodePreorder->rep->rightRepresentative->nodesListHead;

		while(tmpNode != NULL && tmpNode != rightNodePreorder){
			idom[tmpNode->nodesName]=0;
			if(mode == 0) removeChildFromLowHigh(tmpNode->nodesName, prevIdom[tmpNode->nodesName]);
			prevIdom[tmpNode->nodesName]=0;
			level[tmpNode->nodesName]=0;
			derivedGraphInSiblings[tmpNode->nodesName]=0;

			if(tmpNode->rightNode != NULL){
				tmpNode= tmpNode->rightNode;
			}else if(tmpNode->rep->rightRepresentative != NULL){
				tmpNode= tmpNode->rep->rightRepresentative->nodesListHead;
			}else{
				tmpNode= NULL;
			}
		}

		if(rightRepresentativePreorder == NULL){
			leftNodePreorder->rightNode= NULL;
			leftRepresentativePreorder->nodesListTail= leftNodePreorder;
			leftRepresentativePreorder->rightRepresentative= NULL;

			leftRepresentativePreorder->leaves= 0;
			for(struct node* tmpNode= leftRepresentativePreorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) leftRepresentativePreorder->leaves++;
		}else if(leftRepresentativePreorder == rightRepresentativePreorder){
			leftNodePreorder->rightNode= rightNodePreorder;
			rightNodePreorder->leftNode= leftNodePreorder;

			leftRepresentativePreorder->leaves= 0;
			for(struct node* tmpNode= leftRepresentativePreorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) leftRepresentativePreorder->leaves++;
		}else{ // leftRepresentativePreorder != rightRepresentativePreorder
			leftRepresentativePreorder->rightRepresentative= rightRepresentativePreorder;
			rightRepresentativePreorder->leftRepresentative= leftRepresentativePreorder;
			
			leftNodePreorder->rightNode= NULL;
			leftRepresentativePreorder->nodesListTail= leftNodePreorder;
			rightNodePreorder->leftNode= NULL;
			rightRepresentativePreorder->nodesListHead= rightNodePreorder;
			rightRepresentativePreorder->representativesName= rightNodePreorder->nodesName;

			leftRepresentativePreorder->leaves= 0;
			for(struct node* tmpNode= leftRepresentativePreorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) leftRepresentativePreorder->leaves++;

			rightRepresentativePreorder->leaves= 0;
			for(struct node* tmpNode= rightRepresentativePreorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) rightRepresentativePreorder->leaves++;

			if(leftRepresentativePreorder->leaves+rightRepresentativePreorder->leaves < nodesPerRepresentative) mergeRepresentatives(leftRepresentativePreorder, rightRepresentativePreorder);
		}

		// postorder
		rightNodePostorder= nodesTablePostorder[x]->rightNode;

		if(rightNodePostorder == NULL){
			rightNodePostorder= nodesTablePostorder[x]->rep->rightRepresentative->nodesListHead;
			// we can always move right cause root is the last node in postorder list
		}

		leftNodePostorder= nodesTablePostorder[x]->rep->nodesListHead;
		if(leftNodePostorder == NULL && nodesTablePostorder[x]->rep->leftRepresentative != NULL){
			leftNodePostorder= nodesTablePostorder[x]->rep->leftRepresentative->nodesListTail;
		}
		(leftNodePostorder != NULL) ? leftRepresentativePostorder= leftNodePostorder->rep : leftRepresentativePostorder= nodesTablePostorder[x]->rep;

		while(leftNodePostorder != NULL && level[leftNodePostorder->nodesName] == 0 && leftRepresentativePostorder->leftRepresentative != NULL){
			leftRepresentativePostorder= leftRepresentativePostorder->leftRepresentative;
			leftNodePostorder= leftRepresentativePostorder->nodesListHead;
		}

		if(leftNodePostorder-> rep == nodesTablePostorder[x]->rep){
			leftNodePostorder= nodesTablePostorder[x]->leftNode;
			while(leftNodePostorder != NULL && level[leftNodePostorder->nodesName] == 0) leftNodePostorder= leftNodePostorder->leftNode;
		}else{
			leftNodePostorder= leftNodePostorder->rep->nodesListTail;
			while(leftNodePostorder != NULL && level[leftNodePostorder->nodesName] == 0) leftNodePostorder= leftNodePostorder->leftNode;
		}

		if(leftNodePostorder == NULL && leftRepresentativePostorder->leftRepresentative != NULL){
			leftRepresentativePostorder= leftRepresentativePostorder->leftRepresentative;
			leftNodePostorder= leftRepresentativePostorder->nodesListTail;
		}else if(leftNodePostorder == NULL && leftRepresentativePostorder->leftRepresentative == NULL){
			leftRepresentativePostorder= NULL;
		}

		(leftRepresentativePostorder != NULL) ? leftRepresentativePostorder= leftNodePostorder->rep : leftRepresentativePostorder= NULL;
		rightRepresentativePostorder= rightNodePostorder->rep;

		if(leftRepresentativePostorder == NULL){
			rightNodePostorder->leftNode= NULL;
			rightRepresentativePostorder->nodesListHead= rightNodePostorder;
			rightRepresentativePostorder->representativesName= rightNodePostorder->nodesName;
			rightRepresentativePostorder->leftRepresentative= NULL;

			rightRepresentativePostorder->leaves= 0;
			for(struct node* tmpNode= rightRepresentativePostorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) rightRepresentativePostorder->leaves++;
		}else if(leftRepresentativePostorder == rightRepresentativePostorder){
			rightNodePostorder->leftNode= leftNodePostorder;
			leftNodePostorder->rightNode= rightNodePostorder;

			rightRepresentativePostorder->leaves= 0;
			for(struct node* tmpNode= rightRepresentativePostorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) rightRepresentativePostorder->leaves++;
		}else{ // leftRepresentativePostorder != rightRepresentativePostorder
			leftRepresentativePostorder->rightRepresentative= rightRepresentativePostorder;
			rightRepresentativePostorder->leftRepresentative= leftRepresentativePostorder;

			leftNodePostorder->rightNode= NULL;
			leftRepresentativePostorder->nodesListTail= leftNodePostorder;
			rightNodePostorder->leftNode= NULL;
			rightRepresentativePostorder->nodesListHead= rightNodePostorder;
			rightRepresentativePostorder->representativesName= rightNodePostorder->nodesName;

			leftRepresentativePostorder->leaves= 0;
			for(struct node* tmpNode= leftRepresentativePostorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) leftRepresentativePostorder->leaves++;

			rightRepresentativePostorder->leaves= 0;
			for(struct node* tmpNode= rightRepresentativePostorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) rightRepresentativePostorder->leaves++;

			if(leftRepresentativePostorder->leaves+rightRepresentativePostorder->leaves < nodesPerRepresentative) mergeRepresentatives(leftRepresentativePostorder, rightRepresentativePostorder);
		}
	}else{ // node x is still reachable
		//preorder
		leftNodePreorder= nodesTablePreorder[x]->leftNode;
		movingNodeLeftPreorder= nodesTablePreorder[x];
		representativesCounterPreorder= 1;

		if(leftNodePreorder == NULL){
			leftNodePreorder= nodesTablePreorder[x]->rep->leftRepresentative->nodesListTail;
			// we can always move left cause root is the first node in preorder list
		}

		rightNodePreorder= nodesTablePreorder[x]->rightNode;
		if(rightNodePreorder == NULL && nodesTablePreorder[x]->rep->rightRepresentative != NULL){
			representativesCounterPreorder++;
			rightNodePreorder= nodesTablePreorder[x]->rep->rightRepresentative->nodesListHead;
		}
		(rightNodePreorder != NULL) ? rightRepresentativePreorder= rightNodePreorder->rep : rightRepresentativePreorder= nodesTablePreorder[x]->rep;
		
		while(rightNodePreorder != NULL && level[rightNodePreorder->nodesName] > prevLevel && rightRepresentativePreorder->rightRepresentative != NULL){
			if(isChild(x, rightRepresentativePreorder->rightRepresentative->representativesName)){
				representativesCounterPreorder++;
				rightRepresentativePreorder= rightRepresentativePreorder->rightRepresentative;
				rightNodePreorder= rightRepresentativePreorder->nodesListHead;
			}else{
				break;
			}
		}

		if(rightNodePreorder != NULL && rightNodePreorder->rep != rightRepresentativePreorder) rightNodePreorder= rightRepresentativePreorder->nodesListHead;
		while(rightNodePreorder != NULL && level[rightNodePreorder->nodesName] > prevLevel) rightNodePreorder= rightNodePreorder->rightNode;

		if(rightNodePreorder == NULL && rightRepresentativePreorder->rightRepresentative != NULL){
			representativesCounterPreorder++;
			rightRepresentativePreorder= rightRepresentativePreorder->rightRepresentative;
			rightNodePreorder= rightRepresentativePreorder->nodesListHead;
		}

		if(rightNodePreorder != NULL){
			movingNodeRightPreorder= rightNodePreorder->leftNode;
			if(movingNodeRightPreorder == NULL) movingNodeRightPreorder= rightNodePreorder->rep->leftRepresentative->nodesListTail;
		}else{
			movingNodeRightPreorder= rightRepresentativePreorder->nodesListTail;
		}

		cutMovingNodes(leftNodePreorder, rightNodePreorder, movingNodeLeftPreorder, movingNodeRightPreorder, 0);
		movingRepresentativeLeftPreorder= movingNodeLeftPreorder->rep;
		movingRepresentativeRightPreorder= movingNodeRightPreorder->rep;
		
		// move nodes to their new position
		newRepresentativeLeftPreorder= nodesTablePreorder[y]->rep;
		newRepresentativeRightPreorder= NULL;

		if(newRepresentativeLeftPreorder->nodesListTail->nodesName == y){
			newRepresentativeRightPreorder= newRepresentativeLeftPreorder->rightRepresentative;
		}else{
			newNodeLeftPreorder= nodesTablePreorder[y];
			newNodeRightPreorder= newNodeLeftPreorder->rightNode;

			splitRepresentative(newNodeLeftPreorder, newNodeRightPreorder, 0);
			if(newNodeLeftPreorder->rep == leftNodePreorder->rep->leftRepresentative){
				newNodeRightPreorder->rep->tag= newNodeLeftPreorder->rep->tag + ((movingNodeLeftPreorder->rep->tag - newNodeLeftPreorder->rep->tag)/2);
			}

			newRepresentativeRightPreorder= newNodeRightPreorder->rep;
		}

		// postorder
		representativesCounterPostorder= 1;
		rightNodePostorder= nodesTablePostorder[x]->rightNode;
		movingNodeRightPostorder= nodesTablePostorder[x];

		if(rightNodePostorder == NULL){
			rightNodePostorder= nodesTablePostorder[x]->rep->rightRepresentative->nodesListHead;
			// we can always move right cause root is the last node in postorder list
		}

		leftNodePostorder= nodesTablePostorder[x]->leftNode;
		if(leftNodePostorder == NULL && nodesTablePostorder[x]->rep->leftRepresentative != NULL){
			representativesCounterPostorder++;	
			leftNodePostorder= nodesTablePostorder[x]->rep->leftRepresentative->nodesListTail;
		}

		(leftNodePostorder != NULL) ? leftRepresentativePostorder= leftNodePostorder->rep : leftRepresentativePostorder= nodesTablePostorder[x]->rep;

		if(isChild(x, leftRepresentativePostorder->representativesName)){
			while(leftNodePostorder != NULL && level[leftNodePostorder->nodesName] > prevLevel && leftRepresentativePostorder->leftRepresentative != NULL){
				if(isChild(x, leftRepresentativePostorder->leftRepresentative->nodesListTail->nodesName)){
					representativesCounterPostorder++;
					leftRepresentativePostorder= leftRepresentativePostorder->leftRepresentative;
					leftNodePostorder= leftRepresentativePostorder->nodesListTail;
				}else{
					break;
				}
			}
		}

		if(leftNodePostorder != NULL && leftNodePostorder->rep != leftRepresentativePostorder) leftNodePostorder= leftRepresentativePostorder->nodesListTail;
		while(leftNodePostorder != NULL && level[leftNodePostorder->nodesName] > prevLevel) leftNodePostorder= leftNodePostorder->leftNode;

		if(leftNodePostorder == NULL && leftRepresentativePostorder->leftRepresentative != NULL){
			representativesCounterPostorder++;
			leftRepresentativePostorder= leftRepresentativePostorder->leftRepresentative;
			leftNodePostorder= leftRepresentativePostorder->nodesListTail;
		}

		if(leftNodePostorder != NULL){
			movingNodeLeftPostorder= leftNodePostorder->rightNode;
			if(movingNodeLeftPostorder == NULL) movingNodeLeftPostorder= leftNodePostorder->rep->rightRepresentative->nodesListHead;
		}else{
			movingNodeLeftPostorder= leftRepresentativePostorder->nodesListHead;
		}

		cutMovingNodes(leftNodePostorder, rightNodePostorder, movingNodeLeftPostorder, movingNodeRightPostorder, 1);
		movingRepresentativeLeftPostorder= movingNodeLeftPostorder->rep;
		movingRepresentativeRightPostorder= movingNodeRightPostorder->rep;

		// move nodes to their new position
		newNodeLeftPostorder= nodesTablePostorder[y]->leftNode;
		if(newNodeLeftPostorder == NULL && nodesTablePostorder[y]->rep->leftRepresentative != NULL){
			newNodeLeftPostorder= nodesTablePostorder[y]->rep->leftRepresentative->nodesListTail;
		}

		(newNodeLeftPostorder != NULL) ? newRepresentativeLeftPostorder= newNodeLeftPostorder->rep : newRepresentativeLeftPostorder= nodesTablePostorder[y]->rep;

		while(newRepresentativeLeftPostorder->leftRepresentative != NULL && level[newNodeLeftPostorder->nodesName] > level[y]){
			if(isChild(y, newRepresentativeLeftPostorder->leftRepresentative->nodesListTail->nodesName)){
				newRepresentativeLeftPostorder= newRepresentativeLeftPostorder->leftRepresentative;
				newNodeLeftPostorder= newRepresentativeLeftPostorder->nodesListTail;
			}else{
				break;
			}
		}

		if(newNodeLeftPostorder != NULL && newNodeLeftPostorder->rep != newRepresentativeLeftPostorder) newNodeLeftPostorder= newRepresentativeLeftPostorder->nodesListTail;
		while(newNodeLeftPostorder != NULL && level[newNodeLeftPostorder->nodesName] > level[y]) newNodeLeftPostorder= newNodeLeftPostorder->leftNode;

		if(newNodeLeftPostorder == NULL && newRepresentativeLeftPostorder->leftRepresentative != NULL){
			newRepresentativeLeftPostorder= newRepresentativeLeftPostorder->leftRepresentative;
			newNodeLeftPostorder= newRepresentativeLeftPostorder->nodesListTail;
		}

		if(newNodeLeftPostorder != NULL){
			newNodeRightPostorder= newNodeLeftPostorder->rightNode;
			if(newNodeRightPostorder == NULL) newNodeRightPostorder= newNodeLeftPostorder->rep->rightRepresentative->nodesListHead;
		}else{
			newNodeRightPostorder= newRepresentativeLeftPostorder->nodesListHead;
		}

		newRepresentativeRightPostorder= newNodeRightPostorder->rep;

		if(newNodeLeftPostorder != NULL){
			if(newNodeLeftPostorder->rep != newNodeRightPostorder->rep){
				newRepresentativeRightPostorder= newRepresentativeLeftPostorder->rightRepresentative;
			}else{
				splitRepresentative(newNodeLeftPostorder, newNodeRightPostorder, 1);
				newRepresentativeRightPostorder= newNodeRightPostorder->rep;
			}
		}else{
			newRepresentativeLeftPostorder= NULL;
		}

		// preorder
		if(newRepresentativeRightPreorder == NULL){
			idDifferencePreorder= ULLONG_MAX/4 - newRepresentativeLeftPreorder->tag;
		}else{
			idDifferencePreorder= newRepresentativeRightPreorder->tag - newRepresentativeLeftPreorder->tag;
		}

		if(idDifferencePreorder <= representativesCounterPreorder){
			relabelRepresentatives(y, 0, representativesCounterPreorder);

			if(newRepresentativeRightPreorder == NULL){
				idDifferencePreorder= ULLONG_MAX/4 - newRepresentativeLeftPreorder->tag;
			}else{
				idDifferencePreorder= newRepresentativeRightPreorder->tag - newRepresentativeLeftPreorder->tag;
			}
		}

		if(newRepresentativeRightPreorder == NULL){
			newRepresentativeLeftPreorder->rightRepresentative= movingRepresentativeLeftPreorder;
			movingRepresentativeLeftPreorder->leftRepresentative= newRepresentativeLeftPreorder;

			movingRepresentativeRightPreorder->rightRepresentative= NULL;
		}else{
			preorderFlag= true;

			newRepresentativeLeftPreorder->rightRepresentative= movingRepresentativeLeftPreorder;
			movingRepresentativeLeftPreorder->leftRepresentative= newRepresentativeLeftPreorder;

			newRepresentativeRightPreorder->leftRepresentative= movingRepresentativeRightPreorder;
			movingRepresentativeRightPreorder->rightRepresentative= newRepresentativeRightPreorder;
		}

		// postorder
		if(newRepresentativeLeftPostorder == NULL){
			idDifferencePostorder= newRepresentativeRightPostorder->tag;
		}else{
			idDifferencePostorder= newRepresentativeRightPostorder->tag - newRepresentativeLeftPostorder->tag;
		}

		if(idDifferencePostorder <= representativesCounterPostorder){
			relabelRepresentatives(newNodeRightPostorder->nodesName, 1, representativesCounterPostorder);

			if(newRepresentativeLeftPostorder == NULL){
				idDifferencePostorder= newRepresentativeRightPostorder->tag;
			}else{
				idDifferencePostorder= newRepresentativeRightPostorder->tag - newRepresentativeLeftPostorder->tag;
			}
		}

		if(newRepresentativeLeftPostorder == NULL){
			newRepresentativeRightPostorder->leftRepresentative= movingRepresentativeRightPostorder;
			movingRepresentativeRightPostorder->rightRepresentative= newRepresentativeRightPostorder;

			movingRepresentativeLeftPostorder->leftRepresentative= NULL;
		}else{
			postorderFlag= true;

			newRepresentativeRightPostorder->leftRepresentative= movingRepresentativeRightPostorder;
			movingRepresentativeRightPostorder->rightRepresentative= newRepresentativeRightPostorder;

			newRepresentativeLeftPostorder->rightRepresentative=movingRepresentativeLeftPostorder;
			movingRepresentativeLeftPostorder->leftRepresentative= newRepresentativeLeftPostorder;
		}

		// preorder
		tmpRepresentative= movingRepresentativeLeftPreorder;
		representativesCounterPreorder++;

		if(representativesCounterPreorder == 1){
			idsBetweenNodes= idDifferencePreorder/representativesCounterPreorder;
			tmpRepresentative->tag= newRepresentativeLeftPreorder->tag + idsBetweenNodes;
		}else{
			idsBetweenNodes= idDifferencePreorder/representativesCounterPreorder;
			nextId= newRepresentativeLeftPreorder->tag + idsBetweenNodes;

			while(tmpRepresentative != NULL && tmpRepresentative != newRepresentativeRightPreorder){
				tmpRepresentative->tag= nextId;
				nextId+= idsBetweenNodes;
				tmpRepresentative= tmpRepresentative->rightRepresentative;
			}
		}

		// postorder
		tmpRepresentative= movingRepresentativeRightPostorder;
		representativesCounterPostorder++;

		if(representativesCounterPostorder == 1){
			idsBetweenNodes= idDifferencePostorder/representativesCounterPostorder;
			tmpRepresentative->tag= newRepresentativeRightPostorder->tag - idsBetweenNodes;
		}else{
			idsBetweenNodes= idDifferencePostorder/representativesCounterPostorder;
			nextId= newRepresentativeRightPostorder->tag - idsBetweenNodes;

			while(tmpRepresentative != NULL && tmpRepresentative != newRepresentativeLeftPostorder){
				tmpRepresentative->tag= nextId;
				nextId-= idsBetweenNodes;
				tmpRepresentative= tmpRepresentative->leftRepresentative;
			}
		}

		// merge if needed
		// preorder
		if(preorderFlag == true){
			if(newRepresentativeLeftPreorder->leaves+movingRepresentativeLeftPreorder->leaves < nodesPerRepresentative){
				mergeRepresentatives(newRepresentativeLeftPreorder, movingRepresentativeLeftPreorder);
				if(movingRepresentativeRightPreorder == movingRepresentativeLeftPreorder) movingRepresentativeRightPreorder= newRepresentativeLeftPreorder;
			}
			if(newRepresentativeRightPreorder->leaves+movingRepresentativeRightPreorder->leaves < nodesPerRepresentative) mergeRepresentatives(movingRepresentativeRightPreorder, newRepresentativeRightPreorder);
		}

		// postorder
		if(postorderFlag == true){
			if(newRepresentativeLeftPostorder->leaves+movingRepresentativeLeftPostorder->leaves < nodesPerRepresentative){
				mergeRepresentatives(newRepresentativeLeftPostorder, movingRepresentativeLeftPostorder);
				if(movingRepresentativeRightPostorder == movingRepresentativeLeftPostorder) movingRepresentativeRightPostorder= newRepresentativeLeftPostorder;
			}
			if(newRepresentativeRightPostorder->leaves+movingRepresentativeRightPostorder->leaves < nodesPerRepresentative) mergeRepresentatives(movingRepresentativeRightPostorder, newRepresentativeRightPostorder);
		}
	}
}

void updateDominatorTreeLevels(int node){
	struct node* tmpNode= nodesTablePreorder[node]->rightNode;
	struct representative* tmpRep= NULL;

	if(tmpNode == NULL){
		if(nodesTablePreorder[node]->rep->rightRepresentative == NULL){
			tmpNode= NULL;
		}else{
			tmpRep= nodesTablePreorder[node]->rep->rightRepresentative;
			tmpNode= tmpRep->nodesListHead;
		}
	}

	while(tmpNode != NULL && isChild(node, tmpNode->nodesName)){
		level[tmpNode->nodesName]= level[idom[tmpNode->nodesName]]+1;

		if(tmpNode->rightNode != NULL){
			tmpNode= tmpNode->rightNode;
		}else{
			tmpRep= tmpNode->rep->rightRepresentative;
			
			if(tmpRep == NULL){
				break;
			}else{
				tmpNode= tmpRep->nodesListHead;
			}
		}
	}
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
void locateNewParent(int w, int c, int y, int mode){
	int u= 0;
	int vPosition= 0;
	int v= 0;

	noNewParentFlag= false;

	// D'[c,d'(y)]
	if(criticalPathFlag == false){
		int tmp= idom[y];

		while(tmp != idom[c]){
			criticalPathCounter++;
			tmp= idom[tmp];
		}

		tmp= y;
		while(criticalPathCounter != -1){
			criticalPath[criticalPathCounter]= tmp;
			criticalPathCounter--;
			tmp= idom[tmp];
		}
		criticalPathFlag= true;
		criticalPathCounter= 0;
	}

	u= criticalPath[criticalPathCounter];

	while(u != 0){
		if(c != idom[y]){
			vPosition= r_First[w];
			v= r_Target[vPosition];

			while(v != 0){
				if(!isChild(u ,v)){
					if(idom[w] != idom[u] && idom[w] != v){
						idom[w]= idom[u];
						prevLevel= level[w];
						level[w]= level[idom[u]]+1;

						updateDominatorTreeLevels(w);
						checkIncomingEdges(w);
						updateIds(w, idom[w], mode);
						criticalPathCounter= 0;
					}else{
						noNewParentFlag= true;
					}

					return;
				}else{
					vPosition= r_Next[vPosition];
					v= r_Target[vPosition];
				}
			}

			criticalPathCounter++;
			u= criticalPath[criticalPathCounter];
		}else{
			idom[w]= c;
			prevLevel= level[w];
			level[w]= level[c]+1;

			updateDominatorTreeLevels(w);
			if(removeFromDerivedGraph(c, w, 0)){
				derivedGraphInSiblings[w]--;
			}

			addToDerivedGraph(c, w);
			checkIncomingEdges(w);
			updateIds(w, idom[w], mode);

			return;
		}
	}
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
void processQList(int y, int c, int lowHighDominator, int mode){
	int w= 0;

	QListCounter= 0;
	if(c == -1){
		while(QListCounter != nodesInQList){
			w= QList[QListCounter];
			locateNewParent(w, c, y, mode);
			if(noNewParentFlag == false) updateInSiblings(w, c, lowHighDominator, mode);

			QListCounter++;
		}
	}else{
		while(QListCounter != nodesInQList){
			w= QList[QListCounter];

			locateNewParent(w, c, y, mode);
			if(noNewParentFlag == false) updateInSiblings(w, c, lowHighDominator, mode);

			QListCounter++;
		}
	}
}

inline void sortTriples(){
	int nodes= n+1;
	int* Triples2 = new int[3*triplesCounter];
	int* Count = new int[nodes+2];

	for(int i=2; i >= 0; i--){		//do this for every number of the triple
		for(int j=0; j <=nodes; j++) Count[j] = 0; //initialize
		for(int j=0; j < triplesCounter; j++) Count[triples[3*j+i]+1]++;  //count how many times every value apears
		for(int j=1; j <=nodes; j++) Count[j]+= Count[j-1];
		for(int j=0; j < triplesCounter; j++){ //insert triples into array in right order
			int k = Count[triples[3*j+i]];

			Triples2[3*k]   = triples[3*j];
			Triples2[3*k+1] = triples[3*j+1];
			Triples2[3*k+2] = triples[3*j+2];
			Count[triples[3*j+i]]++;
		}

		for (int j=0; j < 3*triplesCounter; j++) triples[j]= Triples2[j]; //copy the triples to the original array
	}

	delete [] Triples2;
	delete [] Count;
}

void processTriples(){
	int x= 0, y= 0;
	int prevX= 0, prevY= 0;

	for(int i= 0; i < triplesCounter; i++){
		if(triples[3*i+2] == 0){
			x= label2preorderDominator[triples[3*i+1]];
		}else{
			y= label2preorderDominator[triples[3*i+2]];

			if((prevX != x || prevY != y) && x != y){
				if(x != 0) addToDerivedGraph(x, y);

				prevX= x;
				prevY= y;
			}else{ // derived arc (x,y) already in derived graph
				int tmpPossition= derivedOutFirst[x], tmpNode= derivedOutTarget[tmpPossition];

				if(x != y){
					while(tmpNode != 0){
						if(tmpNode == y){
							derivedEdgeCounter[tmpPossition]++;
							break;
						}else{
							tmpPossition= derivedOutNext[tmpPossition];
							tmpNode= derivedOutTarget[tmpPossition];
						}
					}
				}
			}
		}
	}
}

void addTriple(int x, int y, int z){
	if(y != 0){
		triples[3*triplesCounter]= x;
		triples[3*triplesCounter+1]= y;
		triples[3*triplesCounter+2]= z;

		triplesCounter++;
	}
}

void resetQList(){
	for(int i= nodesInQList-1; i>=0; i--){
		inQList[QList[i]]= 0;
		QList[i]= 0;
	}

	nodesInQList= 0;
}

void checkDerivedArcFromDominator(int node){
	int tmpPosition= derivedInFirst[node];
	int tmpNode= derivedInTarget[tmpPosition];

	while(tmpNode != 0){
		if(tmpNode == idom[node]){
			derivedArcFromDominator[node]= true;
			return;
		}

		tmpPosition= derivedInNext[tmpPosition];
		tmpNode= derivedInTarget[tmpPosition];
	}
}

void scanNode(int node){
	int tmpPosition= derivedOutLowHighFirst[node];
	int tmpNode= derivedOutLowHighTarget[tmpPosition];
	int tmpDerivedArc1= 0;
	int tmpDerivedArc2= 0;
	bool flagLower= false;
	bool flagHigher= false;
	bool flagInOrder= false;

	while(tmpNode != 0){
		flagInOrder= false;

		if(derivedArcFromDominator[tmpNode] == true){
			flagInOrder= true;
		}else{
			if(inViolatingLowHigh[tmpNode] == false){
				int tmpDerivedPosition= derivedInFirst[tmpNode];
				int tmpDerivedNode= derivedInTarget[tmpNode];
				flagLower= flagHigher= false;

				while(tmpDerivedNode != 0 && flagLower == false && flagHigher == false){
					if(inNeedUpdateLowHigh[tmpDerivedNode] == false){
						if(lowHighId[tmpDerivedNode] > lowHighId[tmpNode]){
							flagHigher= true;
							tmpDerivedArc1= tmpDerivedNode;
						}else{
							flagLower= true;
							tmpDerivedArc2= tmpDerivedNode;
						}

					}

					tmpDerivedPosition= derivedInNext[tmpDerivedPosition];
					tmpDerivedNode= derivedInTarget[tmpDerivedPosition];
				}

				if(flagLower == true && flagHigher == true){
					flagInOrder= true;
				}
			}
		}

		if(flagInOrder == false){
			addToViolatingLowHigh(tmpNode);
		}else if(flagInOrder == true && derivedArcFromDominator[tmpNode] != true){
			bool firstPosition= false;
			bool secondPosition= false;

			if(derivedInLowHigh[tmpNode][0] == tmpDerivedArc1 || derivedInLowHigh[tmpNode][0] == tmpDerivedArc2) firstPosition= true;
			if(derivedInLowHigh[tmpNode][1] == tmpDerivedArc1 || derivedInLowHigh[tmpNode][1] == tmpDerivedArc2) secondPosition= true;
			
			if(firstPosition == false && secondPosition == false){
				removeFromDerivedOutLowHigh(tmpNode, derivedInLowHigh[node][0]);
				removeFromDerivedOutLowHigh(tmpNode, derivedInLowHigh[node][1]);

				addToDerivedOutLowHigh(tmpNode, tmpDerivedArc1);
				derivedInLowHigh[tmpNode][0]= tmpDerivedArc1;
				derivedInLowHighReversePosition[tmpNode][0]= derivedOutLowHighCurrentPosition-1;
				derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= tmpNode;

				addToDerivedOutLowHigh(tmpNode, tmpDerivedArc2);
				derivedInLowHigh[tmpNode][1]= tmpDerivedArc2;
				derivedInLowHighReversePosition[tmpNode][1]= derivedOutLowHighCurrentPosition-1;
				derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= tmpNode;
			}else if(firstPosition == false && secondPosition == true){
				removeFromDerivedOutLowHigh(tmpNode, derivedInLowHigh[node][0]);

				if(derivedInLowHigh[node][1] == tmpDerivedArc1){
					addToDerivedOutLowHigh(tmpNode, tmpDerivedArc2);
					derivedInLowHigh[tmpNode][0]= tmpDerivedArc2;
					derivedInLowHighReversePosition[tmpNode][0]= derivedOutLowHighCurrentPosition-1;
					derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= tmpNode;
				}else{
					addToDerivedOutLowHigh(tmpNode, tmpDerivedArc1);
					derivedInLowHigh[tmpNode][0]= tmpDerivedArc1;
					derivedInLowHighReversePosition[tmpNode][0]= derivedOutLowHighCurrentPosition-1;
					derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= tmpNode;
				}
			}else if(firstPosition == true && secondPosition == false){
				removeFromDerivedOutLowHigh(tmpNode, derivedInLowHigh[node][1]);

				if(derivedInLowHigh[node][0] == tmpDerivedArc1){
					addToDerivedOutLowHigh(tmpNode, tmpDerivedArc2);
					derivedInLowHigh[tmpNode][1]= tmpDerivedArc2;
					derivedInLowHighReversePosition[tmpNode][1]= derivedOutLowHighCurrentPosition-1;
					derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= tmpNode;
				}else{
					addToDerivedOutLowHigh(tmpNode, tmpDerivedArc1);
					derivedInLowHigh[tmpNode][1]= tmpDerivedArc1;
					derivedInLowHighReversePosition[tmpNode][1]= derivedOutLowHighCurrentPosition-1;
					derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= tmpNode;
				}
			}
		}

		tmpPosition= derivedOutLowHighNext[tmpPosition];
		tmpNode= derivedOutLowHighTarget[tmpPosition];
	}
}

void addToNeedUpdateLowHighSorted(int node){
	if(inNeedUpdateLowHighSorted[node] == false){
		needUpdateLowHighSorted[needUpdateLowHighSortedCounter]= node;
		inNeedUpdateLowHighSorted[node]= true;
		needUpdateLowHighSortedCounter++;
	}
}

void dfsNeedUpdateLowHigh(int node){
	int tmpNode, tmpPosition;

	visited[node]= true;
	visitedNodes[visitedNodesCounter]= node;
	visitedNodesCounter++;

	tmpPosition= derivedOutFirst[node];
	tmpNode= derivedOutTarget[tmpPosition];
	while(tmpNode != 0){
		if(visited[tmpNode] == false && inNeedUpdateLowHigh[node] == true) dfsNeedUpdateLowHigh(tmpNode);

		tmpPosition= derivedOutNext[tmpPosition];
		tmpNode= derivedOutTarget[tmpPosition];
	}

	if(inNeedUpdateLowHigh[node] == true && inNeedUpdateLowHighSorted[node] == false){
		needUpdateLowHighSorted[topologicalOrderCounter]= node;
		inNeedUpdateLowHighSorted[node]= true;
		topologicalOrderCounter--;
	}
}

void processNeedUpdateLowHigh(){
	int currentNode= 0;
	bool removeChildFromLowHighFlag= false;

	topologicalOrderCounter= needUpdateLowHighCounter-1;
	for(int i= 0; i < needUpdateLowHighCounter; i++){
		if(visited[needUpdateLowHigh[i]] == false) dfsNeedUpdateLowHigh(needUpdateLowHigh[i]);
	}

	for(int i= 0; needUpdateLowHighSorted[i] != 0; i++) needUpdateLowHigh[i]= needUpdateLowHighSorted[i]; // copy sorted table

	for(int i= 0; needUpdateLowHigh[i] != 0; i++){
		currentNode= needUpdateLowHigh[i];

		removeChildFromLowHighFlag= removeChildFromLowHigh(currentNode, prevIdom[currentNode]);
		if(removeChildFromLowHighFlag == true) addChildToLowHigh(currentNode, idom[currentNode]);
		inLowHighOrder[currentNode]= true;
		inNeedUpdateLowHigh[currentNode]= false;

		prevIdom[currentNode]= idom[currentNode];
	}
}

void updateLowHigh(){
	int tmpCounter= 0;

	tmpCounter= 0;
	while(violatingLowHigh[tmpCounter] != 0){
		scanNode(violatingLowHigh[tmpCounter]);
		addToNeedUpdateLowHigh(violatingLowHigh[tmpCounter]);
		
		tmpCounter++;
	}

	processNeedUpdateLowHigh();
}

void resetLowHighAuxiliariesLists(){
	for(int i= violatingLowHighCounter-1; i>=0; i--){
		inViolatingLowHigh[violatingLowHigh[i]]= false;
		positionInViolatingLowHigh[violatingLowHigh[i]]= 0;
		violatingLowHigh[i]= 0;
	}

	for(int i= needUpdateLowHighCounter-1; i>=0; i--){
		inNeedUpdateLowHigh[needUpdateLowHigh[i]]= false;
		needUpdateLowHigh[i]= 0;

		inNeedUpdateLowHighSorted[needUpdateLowHighSorted[i]]= false;
		needUpdateLowHighSorted[i]= 0;
	}

	for(int i= visitedNodesCounter-1; i>=0; i--){
		visited[visitedNodes[i]]= false;
		visitedNodes[i]= 0;
	}

	violatingLowHighCounter= 0;
	needUpdateLowHighCounter= 0;
	needUpdateLowHighSortedCounter= 0;
	visitedNodesCounter= 0;
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
inline void deleteReachable(int x, int y, int mode){
	int f= x; // the child of d(y) that's an ancestor of x
	int c= 0;
	int levelIdomY= level[idom[y]];
	int tmpLevel= level[x];
	int tmpNode= 0;
	int tmpPosition= 0;
	int value= -1;
	bool flag= true;

	resetQList();
	if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) resetLowHighAuxiliariesLists();
	criticalPathFlag= false;
	prevLevel= level[x];
	value= removeFromDerivedGraph(x, y, 0);

	if(idom[y] != x){
		while(levelIdomY != tmpLevel &&  levelIdomY+1 < tmpLevel){
			f= idom[f];
			tmpLevel= level[f];
		}

		tmpPosition= r_First[y];
		tmpNode= r_Target[tmpPosition];
		while(flag == true && tmpNode != 0){
			if(preorder2labelDominator[f] <= preorder2labelDominator[tmpNode] && preorder2labelDominator[tmpNode] < preorder2labelDominator[f]+size[f]){ // tmpNode descendant of f
				flag= false;
			}else{
				tmpPosition= r_Next[tmpPosition];
				tmpNode= r_Target[tmpPosition];
			}
		}

		if(flag == true && value != 0){
			derivedGraphInSiblings[y]--;
		}
	}

	if(derivedGraphInSiblings[y] >= 2){
		if(mode == 0 && violatingLowHighFlag == true) addToViolatingLowHigh(y);
		if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) updateLowHigh();

		return;
	}else{
		flag= false;

		if(r_Target[r_First[y]] == idom[y]){
			flag= true;
		}else{
			tmpPosition= r_First[y];

			while(r_Target[tmpPosition] != 0 && r_Target[tmpPosition] != idom[y]){
				tmpPosition= r_Next[tmpPosition];

				if(r_Target[tmpPosition] == idom[y]) flag= true;
			}
		}

		if(flag == true){
			if(mode == 0 && violatingLowHighFlag == true) addToViolatingLowHigh(y);
			if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) updateLowHigh();

			return;
		}
	}

	// compute the nca of In(y)
	int z= 0;
	int tmp1= 0;
	int tmp2= 0;
	tmpPosition= r_First[y];
	tmpNode= r_Target[tmpPosition];

	while(level[tmpNode] == 0){ // incoming arc from unreachable node
		tmpPosition= r_Next[tmpPosition];
		tmpNode= r_Target[tmpPosition];
	}

	tmp1= tmpNode;
	tmpPosition= r_Next[tmpPosition];
	tmpNode= r_Target[tmpPosition];

	while(tmpNode != 0 && level[tmpNode] == 0){ // incoming arc from unreachable node
		tmpPosition= r_Next[tmpPosition];
		tmpNode= r_Target[tmpPosition];
	}

	tmp2= tmpNode;
	while(tmp2 != 0 && tmp1 != tmp2){
		(level[tmp1] < level[tmp2]) ? tmp2= idom[tmp2] : tmp1= idom[tmp1];
	}

	z= tmp1;
	tmpPosition= r_Next[tmpPosition];
	tmp2= r_Target[tmpPosition];

	while(tmp2 != 0){
		while(level[tmp2] != 0 && tmp1 != tmp2){
			(level[tmp1] < level[tmp2]) ? tmp2= idom[tmp2] : tmp1= idom[tmp1];
		}
		z= tmp1;

		tmpPosition= r_Next[tmpPosition];
		tmp2= r_Target[tmpPosition];
	}

	if(z == idom[y]){
		if(mode == 0 && violatingLowHighFlag == true) addToViolatingLowHigh(y);
		if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) updateLowHigh();
		return;
	}

	c= z;
	while(levelIdomY+1 != level[c]){
		c= idom[c];
	}

	idom[y]= z;
	prevLevel= level[y];
	level[y]= level[z]+1;

	checkIncomingEdges(y);
	updateIds(y, idom[y], mode);
	
	int lowHighDominatorNode= prevIdom[y]; 
	updateInSiblings(y, c, prevIdom[y], mode);
	updateDominatorTreeLevels(y);
	processQList(y, c, lowHighDominatorNode, mode);

	if(derivedArcFromDominator[y] == false) checkDerivedArcFromDominator(y);
	if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) updateLowHigh();
	prevIdom[y]= idom[y];
}

void constructDerivedfGraph(){
	int nodes= n+1;
	int y= 0;

	for(int i= 1; i <= nodes; i++){
		if(idom[i] != 0){
			addTriple(preorder2labelDominator[idom[i]], preorder2labelDominator[i], 0);
		}
	}

	for(int x= 1; x <= nodes; x++){
		for(int j= First[x]; j != 0; j= Next[j]){
			y= Target[j];

			if(idom[x] != 0 && idom[y] != 0){
				// (algorithm 3 (page 13 Dominator Tree Certification anmd Divergent Spanning Trees))
				if(preorder2labelDominator[y] <= preorder2labelDominator[x] && preorder2labelDominator[x] < preorder2labelDominator[y]+size[y]){ // step 2
					continue; // acyclic
				}else if(x == idom[y]){ // step 3 (x,y) -> derived arc
					addToDerivedGraph(x, y);
				}else{ // step 4
					addTriple(preorder2labelDominator[idom[y]], preorder2labelDominator[x], preorder2labelDominator[y]);
				}
			}
		}
	}

	sortTriples(); // step 5
	processTriples(); // step 6
}

void constructLowHigh(){
	int topologicalNode= 0;
	int derivedArc1= 0;
	int derivedArc2= 0;
	int dominator= 0;
	bool derivedArcFromIdom= false;

	for(int i= topologicalOrderCounter+1; i < n; i++){
		if(idom[topologicalOrder[i]] != 0){
			derivedArc1= 0;
			derivedArc2= 0;

			topologicalNode= topologicalOrder[i];
			inLowHighOrder[topologicalNode]= true;
			derivedArcFromIdom= derivedArcFromDominator[topologicalNode];

			if(topologicalNode != r){
				int tmpPosition= derivedInFirst[topologicalNode];
				int tmpNode= derivedInTarget[tmpPosition];

				while(derivedArcFromIdom == false && derivedArc2 == 0){
					if(tmpNode == idom[topologicalNode]){
						derivedArcFromIdom= true;
					}else if(inLowHighOrder[tmpNode] == true){
						if(derivedArc1 == 0){
							derivedArc1= tmpNode;
						}else{
							derivedArc2= tmpNode;
						}
					}
				
					tmpPosition= derivedInNext[tmpPosition];
					tmpNode= derivedInTarget[tmpPosition];
				}
				
				dominator= idom[topologicalNode];

				if(derivedArcFromIdom == true){
					if(lowHighHead[dominator] == 0){
						lowHighHead[dominator]= topologicalNode;
						giveNodeLowHighId(topologicalNode, 0, 0);
					}else{
						lowHighPrevNode[lowHighHead[dominator]]= topologicalNode;
						lowHighNextNode[topologicalNode]= lowHighHead[dominator];
						lowHighHead[dominator]= topologicalNode;
						giveNodeLowHighId(topologicalNode, 0, lowHighNextNode[topologicalNode]);
					}

					derivedInLowHigh[topologicalNode][0]= idom[topologicalNode];
					derivedInLowHigh[topologicalNode][1]= idom[topologicalNode];
				}else{
					int left= 0;
					int right= 0;

					if(lowHighId[derivedArc1] < lowHighId[derivedArc2]){
						left= derivedArc1;
					}else{
						left= derivedArc2;
					}

					right= lowHighNextNode[left];
					lowHighNextNode[left]= topologicalNode;
					lowHighPrevNode[topologicalNode]= left;

					lowHighPrevNode[right]= topologicalNode;
					lowHighNextNode[topologicalNode]= right;

					giveNodeLowHighId(topologicalNode, left, right);

					addToDerivedOutLowHigh(topologicalNode, derivedArc1);
					derivedInLowHigh[topologicalNode][0]= derivedArc1;
					derivedInLowHighReversePosition[topologicalNode][0]= derivedOutLowHighCurrentPosition-1;
					derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= topologicalNode;

					addToDerivedOutLowHigh(topologicalNode, derivedArc2);
					derivedInLowHigh[topologicalNode][1]= derivedArc2;
					derivedInLowHighReversePosition[topologicalNode][1]= derivedOutLowHighCurrentPosition-1;
					derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= topologicalNode;
				}

				inLowHighChildrenList[topologicalNode]= true;
			}
		}
	}
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
inline void deleteUnreachable(int x, int y, int mode){
	int source= y;

	resetQList();
	if(mode == 0) resetLowHighAuxiliariesLists();

	while(isChild(y, source)){
		int possition= First[source];
		int target= Target[possition];

		while(target != 0){
			if(!isChild(y, target)){
				delete_arc_from_graph(source, target);

				if (idom[source] != 0){
					nca = intersectLevel(source, target);
					if(target != nca && x != source && y != target){
						deleteReachable(source, target, mode);
						resetQList();
					}
				}
			}else{
				prevLevel= level[target];
				removeFromDerivedGraph(source, target, 0);
			}

			possition= Next[possition];
			target= Target[possition];
		}

		if(nodesTablePostorder[source]->leftNode != NULL){
			source= nodesTablePostorder[source]->leftNode->nodesName;
		}else if(nodesTablePostorder[source]->rep->leftRepresentative != NULL){
			source= nodesTablePostorder[source]->rep->leftRepresentative->nodesListTail->nodesName;
		}else{
			break;
		}
	}

	prevLevel= level[y];
	removeFromDerivedGraph(x, y, 1);
	updateIds(y, -1, mode);

	if(mode == 0 && executeProcessNeedUpdateLowHighFlag == false){
		updateLowHigh();
	}

	if(mode == 0) removeChildFromLowHigh(y, prevIdom[y]);
	
	idom[y]= 0;
	prevIdom[y]= 0;
	level[y]= 0;
}

void createLowHighVerifierFile(char *filename){
	char *tmpPosition= strstr(filename, "output.txt");

	if(tmpPosition != NULL){
		strcpy(tmpPosition, "output_lowHigh.txt");
	}else{
		strcpy(filename, "outputLowHigh.txt");
	}

	printf("Low high output file created: %s\n\n", filename);
	FILE *output;
	output= fopen(filename, "w+");

	int edges= 0;
	int tmpPos= 0;
	int tmpNode= 0;

	for(int i= 1; i < n+1; i++){
		tmpPos= First[i];
		tmpNode= Target[tmpPos];

		while(tmpNode != 0){
			edges++;
			tmpPos= Next[tmpPos];
			tmpNode= Target[tmpPos];
		}
	}

	fprintf(output, "p %d %d %d %d\n", n, edges, r, r);

	for(int i= 1; i <= n+1; i++){
		tmpPos= First[i];
		tmpNode= Target[tmpPos];

		while(tmpNode != 0){
			fprintf(output, "a %d %d\n", i, tmpNode);
			tmpPos= Next[tmpPos];
			tmpNode= Target[tmpPos];
		}
	}

	fprintf(output, "d %d %d\n", r, r);
	for(int i= 1; i < n+1; i++){
		tmpNode= lowHighHead[i];

		while(tmpNode != 0){
			fprintf(output, "d %d %d\n", idom[tmpNode], tmpNode);
			tmpNode= lowHighNextNode[tmpNode];
		}
	}

	fclose(output);
}

void deleteArc(int x, int y) {
	int idomy = idom[y];

	if (!idom[x]) return;

	nca = intersectLevel(x, y);

	if (y == nca) return; // y dominates x - nothing else to do
	
	if(x == idomy){ // y may become unreachable
		// test if y is reachable from idomy
		if(isReachable(y)){
			executeProcessNeedUpdateLowHighFlag= true;
			deleteReachable(x, y, UPDATE_LOW_HIGH);
		}else{
			executeProcessNeedUpdateLowHighFlag= false;
			deleteUnreachable(x, y, UPDATE_LOW_HIGH);
		}
	}else{
		executeProcessNeedUpdateLowHighFlag= true;
		deleteReachable(x, y, UPDATE_LOW_HIGH); // y reachable
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
	int current_input_pos= 0;

	while (fgets(line, MAXLINE, input) != NULL) {
		switch (line[0]) {
		case '\n':;
		case '\0': break;
		case 'p':
			if(sscanf(line, "p %d %d %d %d", &n, &m, &r, &dummy) != 4){
				fprintf(stderr, "Error reading graph size (%s).\n", file);
				exit(-1);
			}

			input_file = new int[3*(m+1)];
			break;
		case 'a':
			if (sscanf(line, "a %d %d", &x, &y) != 2) {
				fprintf(stderr, "Error reading graph arc (%s).\n", file);
				exit(-1);
			}

			input_file[current_input_pos++]= x;
			input_file[current_input_pos++]= y;
			input_file[current_input_pos++]= INPUT_a;

			break;
		case 'e': //fprintf(stderr, "read e\n");
			input_file[current_input_pos++]= 0;
			input_file[current_input_pos++]= 0;
			input_file[current_input_pos++]= INPUT_e;

			break;
		case 'i':
			if (sscanf(line, "i %d %d", &x, &y) != 2) {
				fprintf(stderr, "Error reading graph insertion (%s).\n", file);
				exit(-1);
			}

			input_file[current_input_pos++]= x;
			input_file[current_input_pos++]= y;
			input_file[current_input_pos++]= INPUT_i;

			break;
		case 'd':
			if (sscanf(line, "d %d %d", &x, &y) != 2) {
				fprintf(stderr, "Error reading graph deletion (%s).\n", file);
				exit(-1);
			}

			input_file[current_input_pos++]= x;
			input_file[current_input_pos++]= y;
			input_file[current_input_pos++]= INPUT_d;

			break;
		default:
			fprintf(stderr, "Error reading graph (%s).\n", file);
			exit(-1);
		}
	}

	fclose(input);
}

// process input arcs
void processInput(){
	int input_source, input_target, input_type;
	int current_input_pos;

	int lol= 0; // !!!
	for (current_input_pos = 0; current_input_pos <= 3 * m; current_input_pos += 3) {
		input_source = input_file[current_input_pos];
		input_target = input_file[current_input_pos + 1];
		input_type = input_file[current_input_pos + 2];
		switch (input_type) {
		case INPUT_a:
			insert_arc_to_graph(input_source, input_target);
			break;
		case INPUT_e:
			last_arcQueue= 0;
			snca(r, -1);
			initializeDominatorTreeStructures();
			initializeDerivedGraphStructures();
			constructDerivedfGraph();
			constructLowHigh();

			for(int i= n; i >= 0; i--) prevIdom[i]= idom[i];
			for(int i= visitedNodesCounter; i >= 0; i--) visitedNodes[i]= 0;
			visitedNodesCounter= 0;

			break;
		case INPUT_i:
			break;
		case INPUT_d:
			if(input_source == 18301 && input_target == 18300){
				printf("");
			}

			if(idom[input_source] != 0){
				delete_arc_from_graph(input_source, input_target);
				deleteArc(input_source, input_target);
			}

			// !!!
			char command[100];
			lol++;
			if(lol){
				createLowHighVerifierFile(file);
				printf("%d: ", lol);
				sprintf (command, "lowhighVerifier %s >> lol.txt", "outputLowHigh.txt");
				system(command);
			}

			break;
		default:
			fprintf(stderr, "Error reading graph.\n");
			exit(-1);
		}
	}
}

int main(int argc, char *argv[]) {
	if (argc != 2) {
		printf("\n usage: %s < input file>\n\n", argv[0]);
		exit(-1);
	}
	strcpy(file, argv[1]);
	
	printf("%llu\n", ULLONG_MAX);
	readGraph(file);

	#ifdef _WIN32
		std::chrono::duration<double> totalTime;
		auto start = std::chrono::high_resolution_clock::now();
	#elif _linux
		RFWTimer timer(true);
		double t;
	#endif
	
	init(n + 1, m + 1);
	processInput();

	#ifdef _WIN32
		auto finish = std::chrono::high_resolution_clock::now();
		totalTime+= finish-start;
		printf("Total time= %g\n", totalTime);
	#elif _linux
		t = timer.getTime();
		printf("Total time= %g\n", t);
	#endif

	if(UPDATE_LOW_HIGH == 0) createLowHighVerifierFile(file);
}

// decremental-> 5.43 sec
// dec+lowHigh-> 180.9 sec
