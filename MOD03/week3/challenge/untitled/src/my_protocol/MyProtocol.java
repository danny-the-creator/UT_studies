package my_protocol;

import framework.IMACProtocol;
import framework.MediumState;
import framework.TransmissionInfo;
import framework.TransmissionType;

import java.util.*;
import java.util.zip.CheckedOutputStream;

/**
 * A fairly trivial Medium Access Control scheme.
 *
 * @author Jaco ter Braak, University of Twente
 * @version 05-12-2013
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
public class MyProtocol implements IMACProtocol {
    private int id = 0;
    private int index=0;
    private Set<Integer> nodes = new HashSet<>();
    List<Integer> queue = new ArrayList<>(nodes);

    @Override
    public TransmissionInfo TimeslotAvailable(MediumState previousMediumState,
                                              int controlInformation, int localQueueLength) {
        System.out.println("id:"+id);
        System.out.println(nodes);
        if ((nodes.size() < 3)) {       // we have tried to include here all other nodes (their IDs)
            if ((controlInformation == 0) && (id != 0)) {       // if the id to the current node was
                // assigned before and no new IDs where sen,
                // we just transmit the same id to other nodes with the probability of 25%
                if (new Random().nextInt(100) < 25) {
                    return new TransmissionInfo(TransmissionType.NoData, id);
                } else {
                    return new TransmissionInfo(TransmissionType.Silent, 0);
                }
            }
            if (controlInformation != 0) {      // if that's the first iteration, we should not add
                nodes.add(controlInformation);  // 0 to the nodes IDs (they could be anything between 2 and 400)
            }
            if (id == 0) {
                id = new Random().nextInt(2, 400); // if we have no id, we generate the new one
            }
            if (new Random().nextInt(100) < 60) {   // and send this id with the probability of 60%
                return new TransmissionInfo(TransmissionType.NoData, id);
            } else {
                return new TransmissionInfo(TransmissionType.Silent, 0);
            }
        }
            if (queue.size()<4) { // we add the current node to other nodes
                nodes.add(id);
                queue = new ArrayList<>(nodes);
            }
        // No data to send, just be quiet
        if (localQueueLength == 0) {
            System.out.println("SLOT - No data to send.");
            return new TransmissionInfo(TransmissionType.Silent, 0);
        }
        //
        Collections.sort(queue);

        if  (queue.get(index)==id) {// if the current turn is ours, then we send the dato with no problems
            System.out.println("SLOT - Sending data and hope for no collision.");
            index = (index+1)%4; // index increases every time from 0 to 3 after that it goes back to 0
            return new TransmissionInfo(TransmissionType.Data, id);
        } else {
            System.out.println("SLOT - Not sending data to give room for others.");
            index = (index+1)%4;
            return new TransmissionInfo(TransmissionType.Silent, id);
        }
    }

}
