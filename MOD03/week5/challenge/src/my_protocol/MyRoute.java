package my_protocol;

/**
 * Simple object which describes a route entry in the forwarding table.
 * Can be extended to include additional data.
 *
 * Copyright University of Twente,  2013-2024
 *
 **************************************************************************
 *                          = Copyright notice =                          *
 *                                                                        *
 *            This file may ONLY  be distributed UNMODIFIED!              *
 * In particular, a correct solution to the challenge must  NOT be posted *
 * in public places, to preserve the learning effect for future students. *
 **************************************************************************
 */
public class MyRoute {
    public MyRoute(int cost, int nextHop){
        this.cost = cost;
        this.nextHop = nextHop;
    }
    public int nextHop;
    public int cost;
}
