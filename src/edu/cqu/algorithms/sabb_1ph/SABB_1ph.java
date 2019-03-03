package edu.cqu.algorithms.sabb_1ph;

import edu.cqu.core.Message;
import edu.cqu.core.SyncAgent;
import edu.cqu.core.SyncMailer;
import edu.cqu.result.Result;
import edu.cqu.result.ResultCycle;
import edu.cqu.result.annotations.NotRecordCostInCycle;

import java.util.HashMap;
import java.util.Map;

@NotRecordCostInCycle
public class SABB_1ph extends SyncAgent {

    private final static int MSG_CPA = 1;
    private final static int MSG_CPA_BACK = 2;
    private final static int MSG_NEWSOLUTION = 3;
    private final static int MSG_TERNIMATE = 4;
    private final static int MSG_BACKTRACK = 5;

    private final static int LASTID = 10;
    private CPAMsg myCPA;
    private Map<Integer, Integer> bestCPA;
    private int value;
    private int UB;
    private int cpaCost;

    public SABB_1ph(int id, int[] domain, int[] neighbours, Map<Integer, int[][]> constraintCosts, Map<Integer, int[]> neighbourDomains, SyncMailer mailer) {
        super(id, domain, neighbours, constraintCosts, neighbourDomains, mailer);
        myCPA = new CPAMsg();
        bestCPA =new HashMap<>();
        UB = Integer.MAX_VALUE;
    }

    @Override
    protected void initRun() {
        if (id == 1) {
            myCPA.cpa_cost = 0;
            myCPA.CPA.put(id, 0);
            myCPA.UB = Integer.MAX_VALUE;
            sendMessage(new Message(id, id + 1, MSG_CPA, myCPA.clone()));
        }
    }

    @Override
    public void runFinished() {
        ResultCycle res = new ResultCycle();
        res.setAgentValues(id, valueIndex);
        if (id==1) {
            res.setTotalCost(UB);
        }
        mailer.setResultCycle(id, res);
    }

    public int getCost(boolean isPrecede) {
        int precedeCost = 0;
        for (int i : neighbours) {
            if (isPrecede) {
                if (i < id) { // the precede agent
                    if (myCPA.CPA.containsKey(i)) {
                        precedeCost += constraintCosts.get(i)[value][myCPA.CPA.get(i)];
                    } else {
                        throw new RuntimeException("id: " + id + "'s precede cpa is not integrity!");
                    }
                }
            }
            else {
                if (i > id) { // the afterward agent
                    if (myCPA.CPA.containsKey(i)) {
                        precedeCost += constraintCosts.get(i)[value][myCPA.CPA.get(i)];
                    }
                }
            }
        }
        return precedeCost;
    }


    @Override
    public void disposeMessage(Message message) {
        switch (message.getType()) {
            case MSG_CPA : {
                myCPA = (CPAMsg) message.getValue();
                if (myCPA.CPA.containsKey(id)) { // search next sendValue
                    value = myCPA.CPA.get(id);
                    if (++value >= domain.length) {
                        sendMessage(new Message(id, id - 1, MSG_BACKTRACK, null));
                        return;
                    }
                }
                else {
                    value = 0;
                    cpaCost = myCPA.cpa_cost;
                }
                int precedeCost = getCost(true);
                while (cpaCost + precedeCost > myCPA.UB && value < domain.length) { //backtrack
                    ++value;
                    if (value >= domain.length ) {
                        sendMessage(new Message(id, id -1, MSG_BACKTRACK, null));
                        return;
                    }
                    precedeCost = getCost(true);
                }

                if (value >= domain.length) {
                    sendMessage(new Message(id, id -1, MSG_BACKTRACK, null));
                }
                else { //cpa back
                    myCPA.cpa_cost = cpaCost + precedeCost;
                    myCPA.CPA.put(id, value);
                    sendMessage(new Message(id, id - 1, MSG_CPA_BACK, myCPA.clone()));
                }
                break;
            }
            case MSG_CPA_BACK : {
                CPAMsg backCPA = (CPAMsg) message.getValue();
                int lastId = message.getIdSender();
                for (int i : backCPA.CPA.keySet()) {
                    if (lastId < i) {
                        lastId = i;
                    }
                }
                int cost = 0;
                if (value == backCPA.CPA.get(id)) {
                    boolean isNeighbour = false;
                    for (int i : neighbours) {
                        if (lastId == i) {
                            isNeighbour = true;
                            break;
                        }
                    }
                    if (isNeighbour) {
                        cost = constraintCosts.get(lastId)[value][backCPA.CPA.get(lastId)];
                    }
                }
                else {
                    throw new RuntimeException("id:" + id + "'s cpa is wrong!");
                }
                if (backCPA.cpa_cost + cost >= backCPA.UB) {
                    sendMessage(new Message(id, lastId, MSG_CPA, backCPA.clone()));
                }
                else if (id != 1) {//continue cpa back
                    backCPA.cpa_cost += cost;
                    sendMessage(new Message(id, id - 1, MSG_CPA_BACK, backCPA.clone()));
                }
                else if (lastId == LASTID) {//find the lower ub
                    backCPA.UB = backCPA.cpa_cost + cost;
                    for (int i = 1; i <= LASTID; ++i) {
                        sendMessage(new Message(id, i, MSG_NEWSOLUTION, backCPA.clone()));
                    }
                    sendMessage(new Message(id, lastId, MSG_CPA, backCPA.clone()));
                }
                else {
                    backCPA.cpa_cost += cost;
                    sendMessage(new Message(id, lastId + 1, MSG_CPA, backCPA.clone()));
                }
                break;
            }
            case MSG_NEWSOLUTION : {
                CPAMsg tmpCPA = (CPAMsg) message.getValue();
                if (UB > (tmpCPA.UB)) {
                    UB = (tmpCPA.UB);
                    bestCPA = tmpCPA.CPA;
                    myCPA.UB = UB;
                }
                break;
            }
            case MSG_TERNIMATE : {
                stopProcess();
                break;
            }
            case MSG_BACKTRACK : {
                if (++value < domain.length) {
                    int precedeCost = getCost(true);
                    if (cpaCost + precedeCost > myCPA.UB) { //backtrack
                        sendMessage(new Message(id, id - 1, MSG_BACKTRACK, null));
                    } else { //cpa back
                        myCPA.CPA.put(id, value);
                        myCPA.cpa_cost = cpaCost + precedeCost;
                        if (id == 1) {
                            sendMessage(new Message(id, id + 1, MSG_CPA, myCPA.clone()));
                        }
                        else {
                            sendMessage(new Message(id, id - 1, MSG_CPA_BACK, myCPA.clone()));
                        }
                    }
                }
                else {
                    if (id == 1) { // done!
                        for (int i = 1; i <= LASTID; ++i) {
                            sendMessage(new Message(id, i, MSG_TERNIMATE, null));
                        }
                        stopProcess();
                    }
                    else {
                        sendMessage(new Message(id, id - 1, MSG_BACKTRACK, null));
                    }
                }
                break;
            }
        }
    }


    class CPAMsg {
        Map<Integer, Integer> CPA;
        int cpa_cost;
        int UB;

        public CPAMsg() {
            CPA = new HashMap<>();
            cpa_cost = 0;
            UB = Integer.MAX_VALUE;
        }

        protected CPAMsg clone() {
            CPAMsg cpaMsg = new CPAMsg();
            cpaMsg.CPA.putAll(this.CPA);
            cpaMsg.cpa_cost = this.cpa_cost;
            cpaMsg.UB = this.UB;
            return cpaMsg;
        }
    }
}

