package ss.project.server;
import java.io.IOException;
import java.net.Socket;
import java.util.List;
import ss.networking.SocketConnection;

/**
 * Handle the messages, which come from the client and then send it to the clientHandler.
 */
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
    }//good
    /**
     * Handles incoming messages from the client, parsing and processing user commands and chat messages.
     *
     * @param message The incoming message from the client.
     */
    public void handleMessage(String message) {
        List<String> action = List.of(message.split(Protocol.SEPARATOR));
        String command = action.get(0);
        switch (command) {
            case (Protocol.MOVE) -> {
                clientHandler.recieveCHCommand(message);
            }
            case (Protocol.LIST) -> {
                clientHandler.recieveCHCommand(action.get(0));
            }
            case (Protocol.QUEUE)->{
                clientHandler.recieveCHCommand(command);
            }
            case (Protocol.HELLO) -> {
                clientHandler.recieveCHCommand(action.get(0));
                System.out.println(Protocol.HELLO+Protocol.SEPARATOR+"Welcome to server by Danil and Mira");
            }
            case Protocol.LOGIN -> {
                if (clientHandler.getUsername() == null && action.size() == 2 && clientHandler.getHello()) {
                    if (clientHandler.getServer().getNames().contains(action.get(1))) {
                        sendSCCommand(Protocol.ALREADYLOGGEDIN);
                    } else {
                        clientHandler.recieveUsername(action.get(1));
                        System.out.println("Connected: " + clientHandler.getUsername());
                        sendSCCommand(Protocol.LOGIN);
                    }
                }
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
     //* @param name    The sender's username.
     * @param message The chat message to be sent.
     */
    public void sendSCCommand(String message){ // there was a String name as a parameter, removed as we don't need it
        super.sendMessage(message);
    }
}