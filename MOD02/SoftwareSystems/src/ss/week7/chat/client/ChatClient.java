package ss.week7.chat.client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.http.WebSocket;
import java.util.HashSet;
import java.util.Set;
import ss.week7.chat.protocol.Protocol;

public class ChatClient {
    ClientConnection clientConnection;
    Set<ClientListener> listeners = new HashSet<>();
    /**
     * Constructs a new Client with the specified server address and port.
     *
     * @param address The server address.
     * @param port The port number.
     * @throws IOException If an I/O error occurs during the connection setup.
     */
    protected ChatClient(String address, int port) throws IOException {
        clientConnection = new ClientConnection(address, port);
        clientConnection.setChatClient(this);

    }
    /**
     * Closes the client connection to the chat server.
     */
    public synchronized void close() {
        clientConnection.close();
    }
    /**
     * Sends a chat message to the chat server.
     *
     * @param message The message to be sent.
     */
    public void sendChatMessage(String message){
        clientConnection.sendChatMessage(message);
    }
    /**
     * Sends the user's username to the chat server.
     *
     * @param name The username to be sent.
     */
    public void sendUsername(String name){
        clientConnection.sendUsername(name);
    }
    /**
     * Handles disconnection events from the chat server.
     * Notifies all registered listeners about the disconnection.
     */
    public void handleDisconnect() {
        for (ClientListener l: listeners){
            l.connectionLost();
//            System.out.println("Disconnected: ");
        }
    }
    /**
     * Handles incoming chat messages received from the chat server.
     * Notifies all registered listeners about the incoming message.
     *
     * @param name The name of the sender.
     * @param message The content of the chat message.
     */
    public void recieveChatMessage(String name, String message){
        for (ClientListener l: listeners){
            l.chatMessage(name, message);
//            System.out.println(Protocol.FROM+Protocol.SEPARATOR+name+Protocol.SEPARATOR+message);
        }
    }
    /**
     * Adds a listener to the set of listeners.
     *
     * @param listener The listener to be added.
     */
    public void addListener(ClientListener listener){
        listeners.add(listener);
    }
    /**
     * Starts the client connection to the chat server.
     */
    public void start(){
        clientConnection.start();
    }
    /**
     * Removes a listener from the set of listeners.
     *
     * @param listener The listener to be removed.
     */
    public void removeListener(ClientListener listener){
        listeners.remove(listener);
    }
}
