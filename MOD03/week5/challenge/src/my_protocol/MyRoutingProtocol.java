package my_protocol;

import framework.*;

import java.util.*;

/**
 * @version 12-03-2019
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
public class MyRoutingProtocol implements IRoutingProtocol {
    private LinkLayer linkLayer;

    private Set<Integer> neighbours = new HashSet<>();


    // You can use this data structure to store your routing table.
    private HashMap<Integer, MyRoute> myRoutingTable = new HashMap<>();

    @Override
    public void init(LinkLayer linkLayer) {
        this.linkLayer = linkLayer;
    }


    @Override
    public void tick(PacketWithLinkCost[] packetsWithLinkCosts) {
        // Get the address of this node
        int myAddress = this.linkLayer.getOwnAddress();
        // set the newNeighbours from the packetsWithLinkCosts
        Set<Integer> newNeighbours = new HashSet<>();
        for (PacketWithLinkCost packetWithLinkCost: packetsWithLinkCosts){
            newNeighbours.add(packetWithLinkCost.getPacket().getSourceAddress());
        }
        Set<Integer> difElem = new HashSet<>(neighbours);
        difElem.removeAll(newNeighbours);
        // case if some neighbours went down
        if (!difElem.isEmpty()){
            for (int neighbour: difElem) {  // we set the cost for the dead links to infinity
                myRoutingTable.put(neighbour, new MyRoute(Integer.MAX_VALUE, myRoutingTable.get(neighbour).nextHop));

            }
            for (int i : myRoutingTable.keySet()){ // we set the cost for links, which have a dead link in nextHop, to infinity
                int iNextHop = myRoutingTable.get(i).nextHop;
                if (difElem.contains(iNextHop)){
                    myRoutingTable.put(i, new MyRoute(Integer.MAX_VALUE, iNextHop));

                }
            }
        }
        neighbours = new HashSet<>(newNeighbours);// update neighbours
        // set the route from current address to itself to 0
        myRoutingTable.putIfAbsent(myAddress, new MyRoute(0,myAddress));

        // first process the incoming packets; loop over them:
        for (int i = 0; i < packetsWithLinkCosts.length; i++) {
            Packet packet = packetsWithLinkCosts[i].getPacket();
            int linkcost = packetsWithLinkCosts[i].getLinkCost();  // what's the link cost from/to this neighbour?
            int neighbour = packet.getSourceAddress();             // from whom is the packet?
            DataTable dt = packet.getDataTable();                  // other data contained in the packet

            for (int row=0; row < dt.getNRows(); row++){        // for every raw in DataTable we update myRoutingTable
                int dest = dt.getRow(row)[0];
                int cost = dt.getRow(row)[1];
                int nextHop = dt.getRow(row)[2];
                if (myAddress==nextHop||difElem.contains(dest)){
                    continue;
                }
//                System.out.println(row);
                MyRoute myRoute = myRoutingTable.get(dest);
                if (cost == Integer.MAX_VALUE) {
                    // in case one of the link disappeared, and we got this information from the neighbour,
                    // then we should show that this path is not possible

                    if (myRoute.nextHop == neighbour){
                    myRoutingTable.put(dest, new MyRoute(Integer.MAX_VALUE, neighbour));
                    }
                    cost-=(linkcost);
                }
                if (!myRoutingTable.containsKey(dest) || cost+linkcost < myRoute.cost){
                    // in case if we this node didn't know about the destination, or the path he used to know is larger
                    myRoutingTable.put(dest, new MyRoute(cost+linkcost, neighbour));
                }

            }
        }

        // and send out one (or more, if you want) distance vector packets
        // the actual distance vector data must be stored in the DataTable structure
        DataTable dt = new DataTable(3);
        // fill the DataTable with the data from myRoutingTable
        for (int key: myRoutingTable.keySet()){
            MyRoute r = myRoutingTable.get(key);
            Integer[] row = {key, r.cost, r.nextHop};
            dt.addRow(row);
        }

        // next, actually send out the packet, with our own address as the source address
        // .and 0 as the destination address: that's a broadcast to be received by all neighbours
        Packet pkt = new Packet(myAddress, 0, dt);
        this.linkLayer.transmit(pkt);
    }

    public Map<Integer, Integer> getForwardingTable() {
        // This code extracts from your routing table the forwarding table.
        // The result of this method is send to the server to validate and score your protocol.

        // <Destination, NextHop>
        HashMap<Integer, Integer> ft = new HashMap<>();

        for (Map.Entry<Integer, MyRoute> entry : myRoutingTable.entrySet()) {
            ft.put(entry.getKey(), entry.getValue().nextHop);
        }

        return ft;
    }
}
