//---------------------------------------------------------------------------

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include <iostream>

#pragma hdrstop

//---------------------------------------------------------------------------
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/cpp_bin_float.hpp>
#include <boost/rational.hpp>

using namespace std;
using namespace boost::multiprecision;
using boost::rational;



//#define use_rat
//#define use_big_float

#ifdef use_rat
typedef boost::rational<cpp_int> t_prob;
#else
#ifdef use_big_float
typedef number<cpp_bin_float<10>> t_prob;
#else
typedef long double t_prob;

/* the following two can only be used with float */

#define use_log_fact
#define solve_log
#endif
#endif


/* given n dice, each with m sides, roll the dice and count the number of dice with each face value.
 * there are 4 possible games
 * 1: remove a number of dice equal to the maximum face value count. stop when no dice remain.
 * 2: remove a number of dice from the pool corresponding to the number in the face with the smallest count. this could be 0, and is guaranteed to
 *	be 0 when there are fewer dice than faces. terminate when there are fewer dice than faces.
 * 3: remove a number of dice from the pool corresponding to the number in the face with the smallest count that is >= 1. terminate when 0 dice remain.
 * 4: same as 3, but if all dice have the same face value do not remove any. Roll the dice again.
 * How many rolls does it take on average to get to one die?
 */

int ndice;
int nfaces;

typedef enum {e_remove_max, e_remove_min, e_remove_min_non_zero, e_remove_min_not_zero_or_all } t_game_type;


t_game_type game = e_remove_max;

t_prob *fact_table;

int *npartitions;				   /* number of ways to partition i dice into at most nfaces bins */
int ***partition_list;			   /* [idice] [icomb] [ibin] is the number of dice with the same face value. sorted so [idice] [icomb] [ibin] >= [idice] [icomb] [ibin + 1] */
t_prob **partition_bin_perms;
t_prob **partition_color_perms;
t_prob **partition_total_rolls;
t_prob *level_total_rolls;

bool *level_is_terminal_state;

#define n_debugs 10
bool debugs [n_debugs];

#define debug_build_partitions			debugs [0]
#define debug_list_n_partitions			debugs [1]
#define debug_trans_prob_detailed		debugs [2]
#define debug_trans_prob				debugs [3]
#define debug_solve						debugs [4]

/* Number of combinations of ntop things into nbot ways. generalized form with a vector of nnbot things.
 * nbot should sum to ntop.
 */

#ifdef use_log_fact
t_prob ncomb (int ntop, int nnbot, int *nbot) {
	int i;
	t_prob r;

	r = fact_table [ntop];
	for (i = 0; i < nnbot; i++) {
		r -= fact_table [nbot [i]];
	}
	return (exp (r));
}

t_prob log_ncomb (int ntop, int nnbot, int *nbot)
 {	int i;
	t_prob r;

	r = fact_table [ntop];
	for (i = 0; i < nnbot; i++) {
		r -= fact_table [nbot [i]];
	}
	return (r);
}

#else

t_prob ncomb (int ntop, int nnbot, int *nbot) {
	int i;
	t_prob r;

	r = fact_table [ntop];
	for (i = 0; i < nnbot; i++) {
		r /= fact_table [nbot [i]];
	}
	return (r);
}
#endif

t_prob my_powi (t_prob x, int n) {
	t_prob r;
	int i;

	r = 1;
	for (i = 0; i < n; i++) {
		r *= x;
	}
	return r;
}

#ifdef use_log_fact

t_prob log_my_powi (t_prob x, int n)
{  return log (x) * n;
}
#endif

void count_rolls (int idice, int *part, t_prob &bin_perms, t_prob &color_perms, t_prob &total_rolls)
{   int ibin;
	int *bin_face_counts;
	int iface;
	int idie;
	double t;

	bin_perms = ncomb (idice, nfaces, part);

	bin_face_counts = new int [idice + 1];
	for (idie = 0; idie <= idice; idie++)
	{   bin_face_counts [idie] = 0;
	}
	for (iface = 0; iface < nfaces; iface++)
	{   bin_face_counts [part [iface]]++;
	}
	color_perms = ncomb (nfaces, idice + 1, bin_face_counts);

	total_rolls = bin_perms * color_perms;


	delete [] bin_face_counts;

}

#ifdef use_log_fact

t_prob roll_prob_log (int idice, int *part, t_prob log_total_rolls)
{   int ibin;
	int *bin_face_counts;
	int iface;
	int idie;
	double t;
	t_prob bin_perms;
	t_prob color_perms;
	t_prob r;
    t_prob rl;

	bin_perms = log_ncomb (idice, nfaces, part);

	bin_face_counts = new int [idice + 1];
	for (idie = 0; idie <= idice; idie++)
	{   bin_face_counts [idie] = 0;
	}
	for (iface = 0; iface < nfaces; iface++)
	{   bin_face_counts [part [iface]]++;
	}
	color_perms = log_ncomb (nfaces, idice + 1, bin_face_counts);

	rl = bin_perms + color_perms - log_total_rolls;
	if (rl < -500)
	{   r = 0;
	} else
	{   r = exp (rl);
	}

	delete [] bin_face_counts;

	return r;

}
#endif

double my_t_prob_to_double (t_prob p)
{   double d;
	int i;
	double ml, mh, mm;
	t_prob pl, ph, pm;


	if (p == 0)
	{	d = 0;
	} else
	{	d = 1;
		if (p < 0)
		{   d = -1;
			p = -p;
		}
		for (i = 0; i < 1024; i++)
		{   if (p < 1)
			{   p *= 2;
				d *= 0.5;
			}
			if (p >= 2)
			{   p /= 2;
				d *= 2;
			}
		}
		ml = 1;
		mh = 2;
		pl = 1;
		ph = 2;
		for (i = 0; i < 50; i++)
		{   mm = (ml + mh) / 2;
			pm = (pl + ph) / 2;
			if (p > pm)
			{   pl = pm;
				ml = mm;
			} else
			{   ph = pm;
				mh = mm;
			}
		}
		d = d * mm;
	}
	return d;
}

/* how many dice are removed from a given partition */

int nremove (int idice, int *part)
{   int r;
	int i;

	switch (game)
	{
		case e_remove_max:
			r = part [0];
			break;

		case e_remove_min:
			r = part [nfaces - 1];
			break;

		case e_remove_min_non_zero:
			for (i = nfaces - 1; i > 0 && part [i] == 0; i--)
				;
			r = part [i];
			break;

		case e_remove_min_not_zero_or_all:
			for (i = nfaces - 1; i > 1 && part [i] == 0; i--)
				;
			r = part [i];
			break;


	}
	return r;
}

/* build partitions. there are a total of idice dice. we have a partial solution with facecount bins filled.
 * partial_vec lists the bins. ndiceleft is the number of dice remaing to put in the remaining bins. each value must be
 * no larger than binmax to ensure decreasing size of bins. put the count in npart. if create_partition is true
 * then add to partitions.
 */

void build_partitions (int idice, int facecount, int *partial_vec, int ndiceleft, int binmax, int &npart, bool create_partition)
{   int iface;
	int ibincount;
	int ibincountmin;
	int ibincountmax;

	if (facecount == nfaces - 1)
	{   partial_vec [facecount] = ndiceleft;
		if (debug_build_partitions)
		{   printf ("[%d] [%d]", idice, npart);
			for (iface = 0; iface < nfaces; iface++)
			{   printf (" %d", partial_vec [iface]);
			}
		}
		if (create_partition)
		{   for (iface = 0; iface < nfaces; iface++)
			{   partition_list [idice] [npart] [iface] = partial_vec [iface];
			}
			count_rolls (idice, partition_list [idice] [npart], partition_bin_perms [idice] [npart], partition_color_perms [idice] [npart],
					partition_total_rolls [idice] [npart]);
			if (debug_build_partitions)
			{   std::cout << " bin " << partition_bin_perms [idice] [npart] << " col " << partition_color_perms [idice] [npart]
					<< " total " << partition_total_rolls [idice] [npart];
			}
			level_total_rolls [idice] += partition_total_rolls [idice] [npart];
		}
		if (debug_build_partitions)
		{   std::cout << "\n";
		}
		npart++;
	} else {
		/* since bin counts are decreasing, calculate minimum possible value in each bin to ensure we can use all dice.
		 * This is ceil (ndiceleft / (nfaces - facecount))
		 */

		ibincountmin = (ndiceleft + nfaces - facecount - 1) / (nfaces - facecount);
		/* upper bound is min of binmax and ndiceleft */
		if (ndiceleft > binmax)
		{   ibincountmax = binmax;
		} else
		{   ibincountmax = ndiceleft;
		}
		for (ibincount = ibincountmin; ibincount <= ibincountmax; ibincount++)
		{   partial_vec [facecount] = ibincount;
			build_partitions (idice, facecount + 1, partial_vec, ndiceleft - ibincount, ibincount, npart, create_partition);
		}
	}

}

void build_partition_list (int idice, int facecount, int *partial_vec, int ndiceleft, int binmax, int &npart, bool create_partition,
		int **plist, t_prob *prolls, t_prob &total_rolls)

{   int iface;
	int ibincount;
	int ibincountmin;
	int ibincountmax;
	t_prob pcolor_perms;
	t_prob pperms;

	if (facecount == nfaces - 1)
	{   partial_vec [facecount] = ndiceleft;
		if (debug_build_partitions)
		{   printf ("[%d] [%d]", idice, npart);
			for (iface = 0; iface < nfaces; iface++)
			{   printf (" %d", partial_vec [iface]);
			}
		}
		if (create_partition)
		{   for (iface = 0; iface < nfaces; iface++)
			{   plist [npart] [iface] = partial_vec [iface];
			}
			count_rolls (idice, plist [npart], pperms, pcolor_perms, prolls [npart]);
			if (debug_build_partitions)
			{   std::cout << " bin " << pperms << " col " << pcolor_perms << " total " << prolls [npart];
			}
			total_rolls += prolls [npart];
		}
		if (debug_build_partitions)
		{   std::cout << "\n";
		}
		npart++;
	} else {
		/* since bin counts are decreasing, calculate minimum possible value in each bin to ensure we can use all dice.
		 * This is ceil (ndiceleft / (nfaces - facecount))
		 */

		ibincountmin = (ndiceleft + nfaces - facecount - 1) / (nfaces - facecount);
		/* upper bound is min of binmax and ndiceleft */
		if (ndiceleft > binmax)
		{   ibincountmax = binmax;
		} else
		{   ibincountmax = ndiceleft;
		}
		for (ibincount = ibincountmin; ibincount <= ibincountmax; ibincount++)
		{   partial_vec [facecount] = ibincount;
			build_partition_list (idice, facecount + 1, partial_vec, ndiceleft - ibincount, ibincount, npart, create_partition,
				plist, prolls, total_rolls);
		}
	}

}

#ifdef use_log_fact

void add_partition_probs (int idice, int facecount, int *partial_vec, int ndiceleft, int binmax,
		int &npart, t_prob *trans_prob_vec, t_prob log_total_rolls)

{   int iface;
	int ibincount;
	int ibincountmin;
	int ibincountmax;
	t_prob pcolor_perms;
	t_prob pperms;
	t_prob p;
	int ito;

	if (facecount == nfaces - 1)
	{   partial_vec [facecount] = ndiceleft;
		if (debug_build_partitions)
		{   printf ("[%d] [%d]", idice, npart);
			for (iface = 0; iface < nfaces; iface++)
			{   printf (" %d", partial_vec [iface]);
			}
		}
		p = roll_prob_log (idice, partial_vec, log_total_rolls);
		ito = idice - nremove (idice, partial_vec);
		trans_prob_vec [ito] -= p;
		if (debug_trans_prob_detailed)
		{   std::cout << "adding " << p << " to " << ito << " now " << trans_prob_vec [ito] << "\n";
		}
		npart++;
	} else {
		/* since bin counts are decreasing, calculate minimum possible value in each bin to ensure we can use all dice.
		 * This is ceil (ndiceleft / (nfaces - facecount))
		 */

		ibincountmin = (ndiceleft + nfaces - facecount - 1) / (nfaces - facecount);
		/* upper bound is min of binmax and ndiceleft */
		if (ndiceleft > binmax)
		{   ibincountmax = binmax;
		} else
		{   ibincountmax = ndiceleft;
		}
		for (ibincount = ibincountmin; ibincount <= ibincountmax; ibincount++)
		{   partial_vec [facecount] = ibincount;
			add_partition_probs (idice, facecount + 1, partial_vec, ndiceleft - ibincount, ibincount,
					npart, trans_prob_vec, log_total_rolls);
		}
	}

}
#endif

#ifdef use_log_fact
void build_fact_table ()
{   int i;

	fact_table = new t_prob [ndice + 1];
	fact_table [0] = 0;
	for (i = 1; i <= ndice; i++) {
		fact_table [i] = fact_table [i - 1] + log ((double) i);
	}

}
#else

void build_fact_table ()
{   int i;

	fact_table = new t_prob [ndice + 1];
	fact_table [0] = 1;
	for (i = 1; i <= ndice; i++) {
		fact_table [i] = fact_table [i - 1] * i;
	}

}
#endif

void count_partitions ()
{	int *pvec;
	int idice;

	pvec = new int [nfaces];
	npartitions = new int [ndice + 1];
	npartitions [0] = 0;

	for (idice = 1; idice <= ndice; idice++)
	{   npartitions [idice] = 0;
		build_partitions (idice, 0, pvec, idice, idice, npartitions [idice], false);
	}

	delete [] pvec;

}

void alloc_partition_tables ()
{
	partition_list = new int ** [ndice + 1];

	level_total_rolls = new t_prob [ndice + 1];
	partition_bin_perms = new t_prob * [ndice + 1];;
	partition_color_perms = new t_prob * [ndice + 1];;
	partition_total_rolls = new t_prob * [ndice + 1];;
	level_total_rolls = new t_prob [ndice + 1];;

}

void alloc_partition_data (int idice)
{   int ipart;
	int *pvec;

	pvec = new int [nfaces];
	partition_list [idice] = new int * [npartitions [idice]];
	for (ipart = 0; ipart < npartitions [idice]; ipart++)
	{   partition_list [idice] [ipart] = new int [nfaces];
	}

	level_total_rolls [idice] = 0;
	partition_bin_perms [idice] = new t_prob [npartitions [idice]];
	partition_color_perms [idice] = new t_prob [npartitions [idice]];
	partition_total_rolls [idice] = new t_prob [npartitions [idice]];

	npartitions [idice] = 0;
	build_partitions (idice, 0, pvec, idice, idice, npartitions [idice], true);
	if (debug_build_partitions)
	{   std::cout << "total rolls for level " << level_total_rolls [idice] << "\n";
	}


	if (debug_list_n_partitions)
	{	for (idice = 1; idice <= ndice; idice++)
		{   std::cout << "level " << idice << " npart " << npartitions [idice] << "\n";
		}

	}
	if (debug_list_n_partitions)
	{	std::cout << "level " << idice << " npart " << npartitions [idice] << "\n";
	}
	delete [] pvec;
}

void enumerate_partitions ()
{   int i;
	int *pvec;
	int idice;
	int ipart;


	pvec = new int [nfaces];

	alloc_partition_tables ();

	for (idice = 1; idice <= ndice; idice++)
	{   partition_list [idice] = new int * [npartitions [idice]];
		for (ipart = 0; ipart < npartitions [idice]; ipart++)
		{   partition_list [idice] [ipart] = new int [nfaces];
		}
	}

	for (idice = 1; idice <= ndice; idice++)
	{   level_total_rolls [idice] = 0;
		partition_bin_perms [idice] = new t_prob [npartitions [idice]];
		partition_color_perms [idice] = new t_prob [npartitions [idice]];
		partition_total_rolls [idice] = new t_prob [npartitions [idice]];

		npartitions [idice] = 0;
		build_partitions (idice, 0, pvec, idice, idice, npartitions [idice], true);
		if (debug_build_partitions)
		{   std::cout << "total rolls for level " << level_total_rolls [idice] << "\n";
		}
	}
	if (debug_list_n_partitions)
	{	for (idice = 1; idice <= ndice; idice++)
		{   std::cout << "level " << idice << " npart " << npartitions [idice] << "\n";
		}

	}
	delete [] pvec;
}

void solve_matrix ( int n, t_prob **a, t_prob *rhs, t_prob *sol ) {
	int i, j, k;
	t_prob pivotval;

	for (i = 0; i < n; i++)
		sol [i] = rhs [i];
	for (i = 0; i < n; i++)
	{
		pivotval = 1 / a [i] [i];
		for (j = 0; j < n; j++)
		{	a [i] [j] *= pivotval;
		}
		sol [i] *= pivotval;
		for (j = i + 1; j < n; j++)
		{	pivotval = a [j ] [i];
			a [j] [i] = 0;
			for (k = i + 1; k < n; k++)
			{	a [j] [k] -= pivotval * a [i] [k];
			}
			sol [j] -= pivotval * sol [i];
		}
	}
	for (i = n - 1; i >= 0; i--)
	{	for (j = i - 1; j >= 0; j--)
		{	pivotval = a [j] [i];
			a [j] [i] = 0;
			sol [j] -= pivotval * sol [i];
		}
	}
}


void build_terminals ()
{	int idie;


	level_is_terminal_state = new bool [ndice + 1];
	for (idie = 0; idie <= ndice; idie++)
	{   level_is_terminal_state [idie] = false;
	}

	switch (game)
	{
		case e_remove_max:
			level_is_terminal_state [0] = true;
			break;

		case e_remove_min:
			for (idie = 0; idie < nfaces; idie++)
			{   level_is_terminal_state [idie] = true;
			}
			break;

		case e_remove_min_non_zero:
			level_is_terminal_state [0] = true;
			break;

		case e_remove_min_not_zero_or_all:
			level_is_terminal_state [0] = true;
			level_is_terminal_state [1] = true;
			break;


	}

}
void solve_puz ()
{   int ifrom;
	int ito;
	int idie;
	int ipart;
	int **plist;
	int npart;
	int npartmax;
	t_prob *prolls;
	t_prob total_rolls;
	t_prob *state_trans_prob;
	t_prob rhs;
	t_prob *sol;
	t_prob rowsum;
	t_prob p;
	int *pvec;



	build_terminals ();
	/* allocate and init matrix and rhs, sol */

	state_trans_prob = new t_prob [ndice + 1];
	sol = new t_prob [ndice + 1];
	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{	sol [ifrom] = 0;
	}

	plist = new int * [ndice + 1];
	pvec = new int [nfaces];

	/* find out how many partitions in largest case so we can alloc data to hold largest partition set */

	npartmax = 0;
	total_rolls = 0;
	build_partition_list (ndice, 0, pvec, ndice, ndice, npartmax, false, NULL, NULL, total_rolls);
	if (debug_list_n_partitions)
	{	printf ("%d partitions\n", npartmax);
	}
	state_trans_prob = new t_prob [ndice + 1];
	plist = new int * [npartmax];
	for (ipart = 0; ipart < npartmax; ipart++)
	{   plist [ipart] = new int [nfaces];
	}
	prolls = new t_prob [npartmax];



	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{   for (ito = 0; ito <= ifrom; ito++)
		{	state_trans_prob [ito] = 0;
		}
		if (level_is_terminal_state [ifrom])
		{   state_trans_prob [ifrom] = 1;
			rhs = 0;
		}
		else
		{   state_trans_prob [ifrom] = 1;
			rhs = 1;
			npart = 0;
			total_rolls = 0;
			build_partition_list (ifrom, 0, pvec, ifrom, ifrom, npart, true, plist, prolls, total_rolls);
			for (ipart = 0; ipart < npart; ipart++)
			{   	ito = ifrom - nremove (ifrom, plist [ipart]);
				p = prolls [ipart] / total_rolls;
				state_trans_prob [ito] -= p;
				if (debug_trans_prob_detailed)
				{	std::cout << "lev " << ifrom << " part " << ipart << " -> " << ito << " adding to a[" << ifrom << "] [" << ito << "] "
							 << p << " now " << state_trans_prob [ito] << "\n";
				}

			}
			if (debug_trans_prob) {
				printf ("prob table");
				rowsum = 0;		/* row should sum to 1 or we have fucked up */
				for (ito = 0; ito <= ifrom; ito++) {
					cout << " " << state_trans_prob [ito];
					rowsum += state_trans_prob [ito];
				}
				cout << "	  sum " << rowsum << "\n";
			}
			for (ito = 0; ito < ifrom; ito++)
			{   rhs -= sol [ito] * state_trans_prob [ito];
			}
			sol [ifrom] = rhs / state_trans_prob [ito];
		}
	}


	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{
#ifdef use_rat
		std::cout << "lev " << ifrom << " expect " << sol [ifrom] << " float " <<  (boost::rational_cast<double> (sol [ifrom])) << " ";
		std::cout << my_t_prob_to_double (sol [ifrom]) << "\n";
#else
		std::cout << "lev " << ifrom << " expect " << sol [ifrom] << " float " <<   (sol [ifrom]) << "\n";
#endif
	}
}

#ifdef solve_log

void solve_puz_log ()
{   int ifrom;
	int ito;
	int idie;
	int ipart;
	int **plist;
	int npart;
	int npartmax;
	t_prob *prolls;
	t_prob total_rolls;
	t_prob log_total_rolls;
	t_prob log_total_rolls_level;
	t_prob *state_trans_prob;
	t_prob rhs;
	t_prob *sol;
	t_prob rowsum;
	t_prob p;
	int *pvec;



	build_terminals ();
	/* allocate and init matrix and rhs, sol */

	state_trans_prob = new t_prob [ndice + 1];
	sol = new t_prob [ndice + 1];
	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{	sol [ifrom] = 0;
	}

	plist = new int * [ndice + 1];
	pvec = new int [nfaces];

	/* find out how many partitions in largest case so we can alloc data to hold largest partition set */

	npartmax = 0;
	if (debug_list_n_partitions)
	{	build_partition_list (ndice, 0, pvec, ndice, ndice, npartmax, false, NULL, NULL, total_rolls);
		printf ("%d partitions\n", npartmax);
	}
	state_trans_prob = new t_prob [ndice + 1];
	plist = new int * [npartmax];
	for (ipart = 0; ipart < npartmax; ipart++)
	{   plist [ipart] = new int [nfaces];
	}
	prolls = new t_prob [npartmax];



	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{   for (ito = 0; ito <= ifrom; ito++)
		{	state_trans_prob [ito] = 0;
		}
		if (level_is_terminal_state [ifrom])
		{   state_trans_prob [ifrom] = 1;
			rhs = 0;
		}
		else
		{   state_trans_prob [ifrom] = 1;
			rhs = 1;
			npart = 0;
			log_total_rolls_level = log_my_powi (nfaces, ifrom);
//			build_partition_list (ifrom, 0, pvec, ifrom, ifrom, npart, true, plist, prolls, total_rolls);
			add_partition_probs (ifrom, 0, pvec, ifrom, ifrom, npart, state_trans_prob, log_total_rolls_level);
			if (debug_trans_prob) {
				printf ("prob table");
				rowsum = 0;		/* row should sum to 1 or we have fucked up */
				for (ito = 0; ito <= ifrom; ito++) {
					cout << " " << state_trans_prob [ito];
					rowsum += state_trans_prob [ito];
				}
				cout << "	  sum " << rowsum << "\n";
			}
			for (ito = 0; ito < ifrom; ito++)
			{   rhs -= sol [ito] * state_trans_prob [ito];
			}
			sol [ifrom] = rhs / state_trans_prob [ito];
		}
	}


	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{
#ifdef use_rat
		std::cout << "lev " << ifrom << " expect " << sol [ifrom] << " float " <<  (boost::rational_cast<double> (sol [ifrom])) << " ";
		std::cout << my_t_prob_to_double (sol [ifrom]) << "\n";
#else
		std::cout << "lev " << ifrom << " expect " << sol [ifrom] << " float " <<   (sol [ifrom]) << "\n";
#endif
	}
}

#endif

void old_solve_puz ()
{   int ifrom;
	int ito;
	int idie;
	int ipart;
	t_prob **state_trans_prob;
	t_prob *rhs;
	t_prob *sol;
	t_prob rowsum;
	t_prob p;

	count_partitions ();

	enumerate_partitions ();

	build_terminals ();

	state_trans_prob = new t_prob * [ndice + 1];
	rhs = new t_prob [ndice + 1];
	sol = new t_prob [ndice + 1];
	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{   state_trans_prob [ifrom] = new t_prob [ndice + 1];
		for (ito = 0; ito <= ndice; ito++)
		{   state_trans_prob [ifrom] [ito] = 0;
		}
		rhs [ifrom] = 0;
		sol [ifrom] = 0;
	}

	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{   if (level_is_terminal_state [ifrom])
		{   state_trans_prob [ifrom] [ifrom] = 1;
			rhs [ifrom] = 0;
		}
		else
		{   state_trans_prob [ifrom] [ifrom] = 1;
			rhs [ifrom] = 1;
			for (ipart = 0; ipart < npartitions [ifrom]; ipart++)
			{   ito = ifrom - nremove (ifrom, partition_list [ifrom] [ipart]);
				p = partition_total_rolls [ifrom] [ipart] / level_total_rolls [ifrom];
				state_trans_prob [ifrom] [ito] -= p;
				if (debug_trans_prob_detailed)
				{	std::cout << "lev " << ifrom << " part " << ipart << " -> " << ito << " adding to a[" << ifrom << "] [" << ito << "] "
							 << p << " now " << state_trans_prob [ifrom] [ito] << "\n";
				}

			}

		}
	}
	if (debug_trans_prob) {
		printf ("prob table\n");
		for (ifrom = 0; ifrom <= ndice; ifrom++) {
			rowsum = 0;		/* row should sum to 1 or we have fucked up */
			for (ito = 0; ito <= ndice; ito++) {
				cout << " " << state_trans_prob [ifrom] [ito];
				rowsum += state_trans_prob [ifrom] [ito];
			}
			cout << "	  sum " << rowsum << "\n";
		}
	}

	solve_matrix (ndice + 1, state_trans_prob, rhs, sol);

	for (ifrom = 0; ifrom <= ndice; ifrom++)
	{
#ifdef use_rat
		std::cout << "lev " << ifrom << " expect " << sol [ifrom] << " float " << (boost::rational_cast<double> (sol [ifrom])) << " ";
		std::cout << my_t_prob_to_double (sol [ifrom]) << "\n";
#else
		std::cout << "lev " << ifrom << " expect " << sol [ifrom] << " float " << (sol [ifrom]) << "\n";
#endif
	}




}



#pragma argsused

int main(int argc, char* argv[])
{   int i;
	bool solve_fast = false;

	for (i = 0; i < n_debugs; i++) {
		debugs [i] = false;
	}
	while (argc >= 2 && argv [1] [0] == '-')
	{   if (argv [1] [1] == 'd')
		{   if (argv [1] [2] == '\0')
			{	for (i = 0; i < n_debugs; i++)
				{	debugs [i] = true;
				}
			} else
			{   sscanf (argv [1] + 2, "%d", &i);
				debugs [i] = true;
			}
			argc--; argv++;
		} else if (argv [1] [1] == 'g')
		{   sscanf (argv [1] + 2, "%d", &game);
			argc--; argv++;
		} else if (argv [1] [1] == 'f')
		{   solve_fast = true;
		}
	}

	if (argc < 3 || sscanf (argv [1], "%d", &ndice) != 1 || sscanf (argv [2], "%d", &nfaces) != 1) {
		fprintf (stderr, "bad arg\n");
		exit (1);
	}

	build_fact_table ();

//	old_solve_puz ();

#ifdef solve_log
	solve_puz_log ();
#else
	solve_puz ();
#endif



	delete [] fact_table;

	return 0;
}
//---------------------------------------------------------------------------
