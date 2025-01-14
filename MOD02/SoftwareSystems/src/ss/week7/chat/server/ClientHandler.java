package ss.week7.chat.server;

public class ClientHandler {
    private String username;
    private ServerConnection serverConnection;
    private ChatServer server;

    /**
     * Constructs a ClientHandler with the specified ServerConnection and ChatServer instances.
     *
     * @param serverConnection The ServerConnection associated with the client.
     * @param server           The ChatServer instance to which the client is connected.
     */
    public ClientHandler(ServerConnection serverConnection, ChatServer server) {
        this.serverConnection = serverConnection;
        this.server = server;
    }
    /**
     * Receives the username from the client.
     *
     * @param username The username provided by the client.
     */
    public void recieveUsername(String username) {
        this.username = username;
    }
    /**
     * Receives a chat message from the client and forwards it to the ChatServer.
     *
     * @param message The chat message received from the client.
     */
    public void recieveChatMessage(String message) {
        server.sendChatMessage(this, message);
    }

    /**
     * Handles the disconnection event for the client, printing a disconnect message
     * and notifying the ChatServer to remove the client.
     */
    public void handleDisconnect(){
        System.out.println("Disconnect: "+ this.getUsername());
        server.removeClient(this);
    }
    /**
     * Gets the username associated with the client.
     *
     * @return The username of the client.
     */
    public String getUsername(){
        return this.username;
    }
    /**
     * Sends a chat message to the client through its ServerConnection.
     *
     * @param name    The sender's username.
     * @param message The chat message to be sent.
     */
    public void sendChatMessage(String name, String message){
        serverConnection.sendChatMessage(name, message);
    }
}
