#ifndef QUEUE_H
#define QUEUE_H

#include <stdio.h>
#include <stdlib.h>

class SimpleQueue {
	private:
		int maxval, maxsize;
		int *q;
		bool *exists;
		int first, next;
		int count;

	public:
		inline bool isEmpty() {return first==next;}

		inline void insert(int v) {
			count ++;
			if (count > maxsize - 2) fprintf (stderr, "<%d> ", count);
			q[next] = v;
			exists[v] = true;
			next = (next+1) % maxsize;
		}

		inline int remove() {
			int v = q[first];
			first = (first+1) % maxsize;
			exists[v] = false;
			count --;
			return v;	
		}

		inline int getNElements() const {
			return count;
		}

		inline void reset() {
			int v;
			if (count>=maxsize/4) { //very small queues are a special case
				for (v=0; v<=maxval; v++) {exists[v] = false;}
			} else {
				//fprintf (stderr, "Soft reset (%.4f).\n", (double)count / (double)maxsize);
				while (!isEmpty()) {
					exists[remove()] = false;
				}
			}
			count = 0;
			first = next = 0;
		}

		SimpleQueue(int n) {
			maxval = n;
			maxsize = n+2;
			exists = new bool [n+1];
			q = new int [maxsize];
			count = maxsize; //just for reset
			reset();
		}	

		~SimpleQueue() {
			delete [] q;
			delete [] exists;
		}

		inline bool contains(int v) const {
			return exists[v];
		}
};

#endif
