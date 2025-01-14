package my_protocol;

import framework.IRDTProtocol;
import framework.Utils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

/**
 * @version 10-07-2019
 * <p>
 * Copyright University of Twente,  2013-2024
 * <p>
 * *************************************************************************
 * = Copyright notice =                          *
 * *
 * This file may ONLY  be distributed UNMODIFIED!              *
 * In particular, a correct solution to the challenge must  NOT be posted *
 * in public places, to preserve the learning effect for future students. *
 * *************************************************************************
 */
public class MyProtocol extends IRDTProtocol {

    // change the following as you wish:
    static final int HEADERSIZE = 1;   // number of header bytes in each packet
    static final int DATASIZE = 256;   // max. number of user data bytes in each packet
    static final int SWS = 5;
    static final int RWS = 5;

    @Override
    public synchronized void sender() {
        System.out.println("Sending...");

        // read from the input file
        Integer[] fileContents = Utils.getFileContents(getFileID());
        // keep track of where we are in the data
        int filePointer = 0;
        int i = 0;
        HashMap<Integer, Boolean> queue = new HashMap<>();

        //        boolean stop = false;
        int j = 0;
        while (filePointer < fileContents.length) {
            if (queue.size() < SWS) {
                // create a new packet of appropriate size
                int datalen = Math.min(DATASIZE, fileContents.length - filePointer);
                Integer[] pkt = new Integer[HEADERSIZE + datalen];
                // write something random into the header byte
                pkt[0] = i;
                queue.put(i, false);

                // copy databytes from the input file into data part of the packet, i.e., after the header
                System.arraycopy(fileContents, filePointer, pkt, HEADERSIZE, datalen);

                // send the packet to the network layer
                getNetworkLayer().sendPacket(pkt);
                System.out.println("Sent one packet with header=" + pkt[0]);
                i++;
                filePointer += DATASIZE;
            }
            // schedule a timer for 1000 ms into the future, just to show how that works:
            framework.Utils.Timeout.SetTimeout(1000, this, i);
            // and loop and sleep; you may use this loop to check for incoming acks...

            //            if (!stop) {     // if {1 - 0 2-1 3-0}
            try {
                if (j >= 80) {
                    for (var entry : queue.entrySet()) {
                        if (entry.getValue()) {
                            continue;
                        }
                        int datalen = Math.min(DATASIZE,
                                               fileContents.length - (filePointer - (i - entry.getKey()) * DATASIZE));
                        Integer[] pkt = new Integer[HEADERSIZE + datalen];
                        pkt[0] = entry.getKey();
                        System.arraycopy(fileContents,
                                         filePointer - (i - entry.getKey()) * DATASIZE, pkt,
                                         HEADERSIZE, datalen);
                        getNetworkLayer().sendPacket(pkt);
                    }
                }
                Integer[] acknowledgment = getNetworkLayer().receivePacket();
                if (acknowledgment != null) {
                    System.out.println(acknowledgment[0]);
                    //                        synchronized (queue){
                    queue.put(acknowledgment[0], true);

                    for (var entry : queue.entrySet()) {
                        if (!entry.getValue()) {
                            break;
                        }

                        queue.remove(entry.getKey());

                    }
                    //                        }
                }
                Thread.sleep(10);
                j++;
            } catch (InterruptedException ignored) {
            }
            //            }
        }

    }

    @Override
    public void TimeoutElapsed(Object tag) {
        int z = (Integer) tag;
        //        if (z==-1){
        //            stop = true;
        //        }
        // handle expiration of the timeout:
        System.out.println("Timer expired with tag=" + z);
    }

    @Override
    public Integer[] receiver() {
        System.out.println("Receiving...");

        // create the array that will contain the file contents
        // note: we don't know yet how large the file will be, so the easiest (but not most efficient)
        //   is to reallocate the array every time we find out there's more data
        Integer[] fileContents = new Integer[0];

        // loop until we are done receiving the file
        boolean stop = false;
        int i = 0;
        int expected = 0;

        int LFR = 0;
        int LAF = LFR + RWS;
        List<Integer[]> queueRec = new ArrayList<>();
        while (!stop) {

            // try to receive a packet from the network layer
            Integer[] packet = getNetworkLayer().receivePacket();

            // if we indeed received a packet

            if (packet != null) {

                // tell the user
                System.out.println(
                        "Received packet, length=" + packet.length + "  first byte=" + packet[0]);
                //send ack
                Integer[] pkt = new Integer[HEADERSIZE];
                pkt[0] = packet[0];
                getNetworkLayer().sendPacket(pkt);

                // append the packet's data part (excluding the header) to the fileContents array, first making it larger
                if (packet[0] >= expected && packet[0]<= expected+RWS) {        // for queue
                    queueRec.add(packet);       // {1 0 3}
                } else {
                    System.out.println("dropped");
                }
                boolean stop1 = false;
                while (!stop1) {
                    stop1 = true;
                    for (Integer[] pack : queueRec) {
                        if (pack[0] == expected) {
                            int oldlength = fileContents.length;
                            int datalen = pack.length - HEADERSIZE;
                            fileContents = Arrays.copyOf(fileContents, oldlength + datalen);
                            System.arraycopy(pack, HEADERSIZE, fileContents, oldlength, datalen);
                            queueRec.remove(pack);
                            expected++;
                            stop1 = false;
                            break;
                        }

                    }
                }
            } else {
                // wait ~10ms (or however long the OS makes us wait) before trying again
                try {
                    if (i >= 2000) {
                        stop = true;
                    }
                    Thread.sleep(10);
                    i++;
                } catch (InterruptedException e) {
                    stop = true;
                }
            }
        }

        // return the output file
        return fileContents;
    }
}
