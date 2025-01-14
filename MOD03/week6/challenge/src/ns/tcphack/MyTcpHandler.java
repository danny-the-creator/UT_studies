package ns.tcphack;

import java.util.Arrays;

/**
 * @Version: 2016-03-15
 * Copyright: University of Twente, 2015-2024
 *
 **************************************************************************
 *                          = Copyright notice =                          *
 *                                                                        *
 *            This file may ONLY  be distributed UNMODIFIED!              *
 * In particular, a correct solution to the challenge must  NOT be posted *
 * in public places, to preserve the learning effect for future students. *
 **************************************************************************
 */
 
class MyTcpHandler extends TcpHandler {
	public static void main(String[] args) {
		new MyTcpHandler();
	}
	public MyTcpHandler() {
		super();

		boolean done = false;

		// array of bytes in which we're going to build our packet:
		int[] txpkt = new int[82];		// 40 bytes long for now, may need to expand this later

		txpkt[0] = 0x60;	// first byte of the IPv6 header contains version number in upper nibble
		// fill in the rest of the packet yourself...:
		txpkt[1] = 0x0;
		txpkt[2] = 0x0;
		txpkt[3] = 0x0;
//		Payload length
		txpkt[4] = 0x0;
		txpkt[5] = 0x2a;
//		Next header
		txpkt[6] = 253;
//		HOP LIMIT
		txpkt[7] = 30;

//		SRC: 2001:67c:2564:a317:919c:c7ca:5439:9532

		txpkt[8] = 0x20;
		txpkt[9] = 0x01;
		txpkt[10] = 0x06;
		txpkt[11] = 0x7c;
		txpkt[12] = 0x25;
		txpkt[13] = 0x64;
		txpkt[14] = 0xa3;
		txpkt[15] = 0x17;
		txpkt[16] = 0x91;
		txpkt[17] = 0x9c;
		txpkt[18] = 0xc7;
		txpkt[19] = 0xca;
		txpkt[20] = 0x54;
		txpkt[21] = 0x39;
		txpkt[22] = 0x95;
		txpkt[23] = 0x32;

//		DST:
		txpkt[24] = 0x20;
		txpkt[25] = 0x01;
		txpkt[26] = 0x06;
		txpkt[27] = 0x10;
		txpkt[28] = 0x19;
		txpkt[29] = 0x08;
		txpkt[30] = 0xff;
		txpkt[31] = 0x02;
		txpkt[32] = 0xbf;
		txpkt[33] = 0xdf;
		txpkt[34] = 0x45;
		txpkt[35] = 0x92;
		txpkt[36] = 0xd7;
		txpkt[37] = 0xfb;
		txpkt[38] = 0xfa;
		txpkt[39] = 0xfe;

//		DATA:				TCP
		txpkt[40] = 0x55;	//srs port
		txpkt[41] = 0x10;

		txpkt[42] = 0x1e;	// dest port
		txpkt[43] = 0x1e;

		txpkt[44] = 0x00;	// Seq num
		txpkt[45] = 0x00;
		txpkt[46] = 0x00;
		txpkt[47] = 0x56;

		txpkt[48] = 0x00;	// Ack num
		txpkt[49] = 0x00;
		txpkt[50] = 0x00;
		txpkt[51] = 0x00;

		txpkt[52] = 0x60;	// data offset, reserved
		txpkt[53] = 0x02;	// control flags	Syn on

		txpkt[54] = 0x00;	// window size
		txpkt[55] = 0xff;

		txpkt[56] = 0x00;	// checksum
		txpkt[57] = 0x00;

		txpkt[58] = 0x00;	// urgent pointer
		txpkt[59] = 0x00;

		txpkt[60] = 0x00;	//options
		txpkt[61] = 0x00;
		txpkt[62] = 0x00;
		txpkt[63] = 0x00;


		this.sendData(txpkt);	// send the packet

		while (!done) {
			// check for reception of a packet, but wait at most 500 ms:
			int[] rxpkt = this.receiveData(500);
			if (rxpkt.length==0) {
				// nothing has been received yet
				System.out.println("Nothing...");
				continue;
			}
			if (rxpkt[53] == 0x12) {		// if Ack and Syn is set to 1
				txpkt[44] = rxpkt[48];    // Seq num is set to the ack num we received
				txpkt[45] = rxpkt[49];
				txpkt[46] = rxpkt[50];
				txpkt[47] = rxpkt[51];
				// the ack num, we should send (seq num we received + tcp data length)
				int ack = (rxpkt[44] << 24) + (rxpkt[45] << 16) + (rxpkt[46] << 8) + rxpkt[47] + (rxpkt[4] << 8) + rxpkt[5];

				txpkt[48] = ack >>> 24;    // Ack num is set to the sum of seq num and tsp data we received
				txpkt[49] = (ack >>> 16) & 0xff;
				txpkt[50] = (ack >>> 8) & 0xff;
				txpkt[51] = ack & 0xff;

				txpkt[53] = 0x10;    // control flags	Ack on
			}

				byte[] get = ("GET / HTTP/1.0\r\n\r\n").getBytes();	// bytes of the request we should send

				for (int i = 0; i < get.length; i++) {	// add data of the request
					txpkt[i + 64] = get[i];
				}
				this.sendData(txpkt);

			// something has been received
			int len=rxpkt.length;

			// print the received bytes:
			int i;
			System.out.print("Received "+len+" bytes: ");
			for (i=0;i<len;i++) System.out.print(rxpkt[i]+" ");
			System.out.println("");

			try {
				Thread.sleep(300);	// we have to set some delay in order to not crash the server
			} catch (InterruptedException e) {
				throw new RuntimeException(e);
			}
		}   
	}
}
