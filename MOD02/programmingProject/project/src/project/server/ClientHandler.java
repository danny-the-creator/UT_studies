package project.server;

import project.game.model.GameDnB;

/**
 * Represents the user from the server side. Connects server with the serverConnection
 */
public class ClientHandler {
    private String username;
    private ClientHandler partner = null;


    private final ServerConnection serverConnection;
    private final Server server;
    private boolean hello = false;
    public GameDnB game = null;

    /**
     * Constructs a ClientHandler with the specified ServerConnection and ChatServer instances.
     *
     * @param serverConnection The ServerConnection associated with the client.
     * @param server           The ChatServer instance to which the client is connected.
     */
    public ClientHandler(ServerConnection serverConnection, Server server) {
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
    public void recieveCHCommand(String message) {
        server.sendServerCommmand(this, message);
    }

    /**
     * Handles the disconnection event for the client, printing a disconnect message
     * and notifying the ChatServer to remove the client.
     */
    public void handleDisconnect() {
        System.out.println("Disconnected client: " + this.getUsername());
        if (this.getPartner() != null) {
            partner.sendCHCommand(
                    Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.DISCONNECT
                            + Protocol.SEPARATOR + partner.getUsername());
            this.getPartner().setPartner(null);
        }
        server.removeClient(this);
    }

    /**
     * Gets the username associated with the client.
     *
     * @return The username of the client.
     */
    public String getUsername() {
        return this.username;
    }

    /**
     * Sends a chat message to the client through its ServerConnection.
     * <p>
     * //* @param name    The sender's username.
     *
     * @param message The chat message to be sent.
     */
    public void sendCHCommand(String message) { //there was a String name as param
        serverConnection.sendSCCommand(message);
    }

    public ClientHandler getPartner() {
        return this.partner;
    }

    public void setPartner(ClientHandler partner) {
        this.partner = partner;
    }

    public void trueHello() {
        hello = true;
    }

    public boolean getHello() {
        return hello;
    }

    public Server getServer() {
        return server;
    }
}
