/**
 * LongestPrefixMatcher.java
 * <p>
 * Version: 2019-07-10
 * Copyright University of Twente,  2015-2024
 * <p>
 * *************************************************************************
 * = Copyright notice =                          *
 * *
 * This file may ONLY  be distributed UNMODIFIED!              *
 * In particular, a correct solution to the challenge must  NOT be posted *
 * in public places, to preserve the learning effect for future students. *
 * *************************************************************************
 */

package lpm;

import java.nio.Buffer;
import java.util.*;

public class LongestPrefixMatcher {
    /**
     * You can use this function to initialize variables.
     */
    private Map<Integer, List<Integer[]>> routes = new HashMap<>();

    public LongestPrefixMatcher() {

    }

    /**
     * Looks up an IP address in the routing tables
     * @param ip The IP address to be looked up in integer representation
     * @return The port number this IP maps to
     */
    public int lookup(int ip) {
        List<Integer[]> ports;
        for (int i = 0; i < 25; i++) {      // Since prefixLength is always greater or equal to 8,
            // we don't need to check if our IP was shifted more than 24 times
            if ((ports = routes.get(ip))!= null) {  // if we found our shifted IP in routes,
                                        // then the port we are looking for is one of its values
                for (Integer[] port : ports){
                    if (port[0] == (32 - i)){// we check if the ip was shifted as many times, as the key in routes
                        return port[1];
                    }
                }
            }
            ip = ip >>> 1;// Since the ip is not in route keys, we need to ignore one more least significant bit
        }
        return -1;
    }

    /**
     * Adds a route to the routing tables
     * @param ip The IP the block starts at in integer representation
     * @param prefixLength The number of bits indicating the network part
     *                     of the address range (notation ip/prefixLength)
     * @param portNumber The port number the IP block should route to
     */
    public void addRoute(int ip, byte prefixLength, int portNumber) {
        int shortIP = ip >>> (32 - prefixLength);
        routes.computeIfAbsent(shortIP, k -> new ArrayList<>()); // if absent, adds an empty List to the routes
        Integer[] x = {Integer.parseInt(String.valueOf(prefixLength)), portNumber};
        // array has only 2 values: prefixLength and portNumber, and won't be changed later
        routes.get(shortIP).add(x);
    }

    /**
     * This method is called after all routes have been added.
     * You don't have to use this method but can use it to sort or otherwise
     * organize the routing information, if your datastructure requires this.
     */
    public void finalizeRoutes() {
        // TODO: Optionally do something
    }

    /**
     * Converts an integer representation IP to the human readable form
     * @param ip The IP address to convert
     * @return The String representation for the IP (as xxx.xxx.xxx.xxx)
     */
    private String ipToHuman(int ip) {
        return Integer.toString(ip >> 24 & 0xff) + "." + Integer.toString(
                ip >> 16 & 0xff) + "." + Integer.toString(ip >> 8 & 0xff) + "." + Integer.toString(
                ip & 0xff);
    }

    /**
     * Parses an IP
     * @param ipString The IP address to convert
     * @return The integer representation for the IP
     */
    private int parseIP(String ipString) {
        String[] ipParts = ipString.split("\\.");

        int ip = 0;
        for (int i = 0; i < 4; i++) {
            ip |= Integer.parseInt(ipParts[i]) << (24 - (8 * i));
        }

        return ip;
    }
}
