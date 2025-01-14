package ss.week7.chat.client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import ss.networking.SocketConnection;
import ss.week7.chat.protocol.Protocol;

public class ClientConnection extends SocketConnection {
    ChatClient chatClient;
    /**
     * Constructs a new ClientConnection with the specified host and port.
     *
     * @param host The host address of the chat server.
     * @param port The port number of the chat server.
     * @throws IOException If an I/O error occurs during the connection.
     */
    protected ClientConnection(String host, int port) throws IOException {
        super(host, port);
    }
    /**
     * Handles incoming chat messages received from the chat server.
     *
     * @param message The incoming message from the server.
     */
    @Override
    protected void handleMessage(String message) {
        String[] sp = message.split(Protocol.SEPARATOR);
        chatClient.recieveChatMessage(sp[1],sp[2]);
    }
    /**
     * Handles disconnection events from the chat server.
     */
    @Override
    protected void handleDisconnect() {
        chatClient.handleDisconnect();

    }
    /**
     * Closes the client connection to the chat server.
     */
    public void close(){
        super.close();
    }
    /**
     * Sends a chat message to the chat server.
     *
     * @param message The message to be sent.
     */
    public void sendChatMessage(String message){
        super.sendMessage(Protocol.SAY+Protocol.SEPARATOR+message);
    }
    /**
     * Sends the user's username to the chat server.
     *
     * @param name The username to be sent.
     */
    public void sendUsername(String name){
        super.sendMessage(Protocol.USER+Protocol.SEPARATOR+name);
    }
    /**
     * Sets the associated Client for handling events.
     *
     * @param client The Client instance to be associated with this connection.
     */
    public void setChatClient(ChatClient client){
        chatClient = client;

    }
}
