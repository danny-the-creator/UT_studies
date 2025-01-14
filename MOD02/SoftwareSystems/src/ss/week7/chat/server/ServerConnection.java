package ss.week7.chat.server;

import java.io.IOException;
import java.net.Socket;
import java.util.List;
import ss.networking.SocketConnection;
import ss.week7.chat.protocol.Protocol;

public class ServerConnection extends SocketConnection {
    ClientHandler clientHandler;
    /**
     * Constructs a ServerConnection with the specified Socket.
     *
     * @param socket The Socket representing the communication link with the client.
     * @throws IOException If an I/O error occurs while creating the ServerConnection.
     */
    protected ServerConnection(Socket socket) throws IOException {
        super(socket);
    }
    /**
     * Handles incoming messages from the client, parsing and processing user commands and chat messages.
     *
     * @param message The incoming message from the client.
     */
    public void handleMessage(String message) {
        //        System.out.println(message);
        List<String> action = List.of(message.split(Protocol.SEPARATOR));
        if (action.size() != 2) { return; }
        String command = action.get(0);
        String text = action.get(1);
        switch (command) {
            case Protocol.USER -> {
                if (clientHandler.getUsername() == null) {
                    clientHandler.recieveUsername(text);
                    System.out.println("Connected: "+clientHandler.getUsername());
                }
//                clientHandler.recieveUsername(text);
            }
            case Protocol.SAY -> {
                if (clientHandler.getUsername() != null) {
                    clientHandler.recieveChatMessage(text);
                }
//                clientHandler.recieveChatMessage(text);
            }
        }
    }
    /**
     * Handles the disconnection event, delegating to the associated ClientHandler.
     */
    public void handleDisconnect() {
        clientHandler.handleDisconnect();
    }
    /**
     * Sets the ClientHandler associated with this ServerConnection.
     *
     * @param client The ClientHandler instance to be associated with this ServerConnection.
     */
    public void setClientHandler(ClientHandler client) {
        clientHandler = client;
    }
    /**
     * Sends a chat message to the connected client through the ServerConnection.
     *
     * @param name    The sender's username.
     * @param message The chat message to be sent.
     */
    public void sendChatMessage(String name, String message){
        super.sendMessage(Protocol.FROM + Protocol.SEPARATOR + name + Protocol.SEPARATOR + message);
//        super.sendMessage(message);
    }
}
