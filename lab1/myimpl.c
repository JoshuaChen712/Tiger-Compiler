#include "prog1.h"
#include "string.h"
#include <stdio.h>
int maxargs(A_stm stm)
{
	//TODO: put your code here.
	if(stm->kind==A_compoundStm)
	{
		A_stm leftStm=stm->u.compound.stm1;
		A_stm rightStm=stm->u.compound.stm2;
		int leftmax = maxargs(leftStm);
		int rightmax=maxargs(rightStm);
		return leftmax>rightmax? leftmax:rightmax;
	}
	else if(stm->kind==A_assignStm){
		if(stm->u.assign.exp->kind==A_eseqExp){
			return maxargs(stm->u.assign.exp->u.eseq.stm);
		}
		else
		{
			return 0;
		}
	}
	else{
		int count=1;
	    A_expList explist=stm->u.print.exps;
        A_expList next=explist;
		while(next->kind!=A_lastExpList){
			next=next->u.pair.tail;
			count++;
		}
		next=explist;
		while(next->kind!=A_lastExpList){
            if(next->u.pair.head->kind==A_eseqExp){
			    int tmp=maxargs(next->u.pair.head->u.eseq.stm);
				count = tmp >count?tmp:count;
			}
			next=next->u.pair.tail;
		}
		if(next->u.last->kind==A_eseqExp){
              int tmp=maxargs(next->u.last->u.eseq.stm);
			  count=count>tmp?count:tmp;
		}
		return count;
	}
}

typedef struct table *Table_;
struct table{string id;int value;Table_ tail;};
Table_ Table(string id,int value,Table_ tail){
	Table_ t=checked_malloc(sizeof(*t));
	t->id=id;
	t->value=value;
	t->tail=tail;
	return t;
}

int lookup(Table_ t, string key){
    Table_ next=t;
	while(next!=NULL){
		if(!strcmp(next->id,key)){
			return next->value;
		}
		next=next->tail;
	}
}

Table_ interpStm(A_stm s,Table_ t);

typedef struct intAndTable{int i;Table_ t;} *IntAndTable_;
IntAndTable_ IntAndTable(int i,Table_ t){
	IntAndTable_ iandt =checked_malloc(sizeof(*iandt));
	iandt->i =i;
	iandt->t=t;
	return iandt;
}
IntAndTable_ interpExp(A_exp e,Table_ t);

Table_ interpStm(A_stm s,Table_ t){
   if(s->kind==A_assignStm){
	   IntAndTable_ iandt =interpExp(s->u.assign.exp,t);
	   return Table(s->u.assign.id,iandt->i,iandt->t);
   }
   else if(s->kind==A_compoundStm){
	   Table_ new_t =interpStm(s->u.compound.stm1,t);
	   return interpStm(s->u.compound.stm2,new_t);
   }

   else{
	   A_expList explist=s->u.print.exps;
	   A_expList next=explist;
	   Table_ new_t =t;
	   while(next->kind!=A_lastExpList){
		   IntAndTable_ iandt =interpExp(explist->u.pair.head,new_t);
		   new_t =iandt->t;
		   next=next->u.pair.tail;
		   printf("%d",iandt->i);
	   }
	   IntAndTable_ iandt = interpExp(next->u.last,new_t);
	   new_t = iandt->t;
	   printf("%d\n",iandt->i);
	   return new_t;
   }
}

IntAndTable_ interpExp(A_exp e,Table_ t){
	if(e->kind==A_idExp)
	{
		return IntAndTable(lookup(t,e->u.id),t);
	}
	else if(e->kind==A_numExp){
		return IntAndTable(e->u.num,t);
	}
	else if(e->kind==A_opExp){
		int result =0;
		IntAndTable_ left_iandt=interpExp(e->u.op.left,t);
		IntAndTable_ right_iandt=interpExp(e->u.op.right,left_iandt->t);
		switch (e->u.op.oper)
		{
		case A_plus:
		    result=left_iandt->i+right_iandt->i;
			break;
		case A_minus:
		    result=left_iandt->i-right_iandt->i;
		    break;
		case A_times:
		    result=left_iandt->i*right_iandt->i;
			break;
		case A_div:
		    result=left_iandt->i/right_iandt->i;
			break;
		default:
			break;
		}
		return IntAndTable(result,right_iandt->t);
	}
	else{
		Table_ new_table=interpStm(e->u.eseq.stm,t);
		return interpExp(e->u.eseq.exp,new_table);
	}
}

void interp(A_stm stm)
{
	//TODO: put your code here.
	Table_ table=NULL;
	interpStm(stm,table);
}
