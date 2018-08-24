#ifndef PRFIFO_H
#define PRFIFO_H
#include "prfgraph.h"
#include "simplequeue.h"

//typedef int TFlow;

typedef struct {
	int d;    //distance label
	TFlow e;  //excess
} PRData;


class PushRelabelFifo {
	// Push flow along the path 'current' arcs as much as possible
	int GolTarSend (PRData *vertex, int v, int &npushes, SimpleQueue *q);

	//run bfs on the reverse residual graph from r
	int bfs (int r, PRData *vertex, PRFGraph *g, int *queue, int &next, int &work, SimpleQueue *flowq);

	//initialization: push flow out of the source
	void GolTarPreprocess (PRFGraph *g, PRData *vertex, SimpleQueue *q);

	inline void resetStats() {
		npushes = nrelabels = nupdates = 0;
	}

	TFlow GolTarFlow (bool *sinkside);

public:
	PRFGraph *g;
	double workfactor; //how often should distance labels be recomputed?
	bool use_sort;
	bool just_init;
	bool report;
	int npushes;
	int nrelabels; 
	int nupdates;

	PushRelabelFifo () {
		use_sort = false;
		just_init = false;
		report = false;
		workfactor = 0.3;
		g = NULL;
		resetStats();
	}

	//Maxflow Algorithm
	TFlow GolTarFlow (PRFGraph *_g, bool _report, bool *sinkside) {
		g = _g;
		report = _report;
		return GolTarFlow (sinkside);
	}


	double findMinCut (
		long input_nvertices,
		long input_narcs,
		long input_source,
		long input_sink,
		PRFArc *input_arcs,
		bool *sink_side
	) {
		g = new PRFGraph();
		if (use_sort) {
			g->InitializeSort(input_nvertices, input_narcs, input_source, input_sink, input_arcs);
		} else {
			g->InitializeBasic(input_nvertices, input_narcs, input_source, input_sink, input_arcs);
		}
		TFlow flow = just_init ? 0 : GolTarFlow(g, report, sink_side);
		//delete g;
		//g = NULL;
		return flow; //GolTarFlow (&g, report, sink_side);
	}

	double findMinCutUndirected (
		long input_nvertices,
		long input_nedges,
		long input_source,
		long input_sink,
		PRFArc *input_arcs,
		bool *sink_side
	) {
		g = new PRFGraph();
		g->InitializeUndirected(input_nvertices, input_nedges, input_source, input_sink, input_arcs);

		TFlow flow = just_init ? 0 : GolTarFlow (g, report, sink_side);
		delete g;
		g = NULL;
		return flow;
	}
};

#endif

