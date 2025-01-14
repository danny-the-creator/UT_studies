package project.client;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import project.game.model.GameDnB;

/**
 * Represents a client, which will be able to connect to the server and play the game.
 */
public class Client {
    ClientConnection clientConnection;
    private GameDnB game = null;
    private final Set<ClientListener> listeners = new HashSet<>();
    public String playAI = null;      // shows the AI difficulty or null if players don't need help
    public ClientTUI tui;
    public boolean loggedIn = false;        // shows if user is loggedIn
    public boolean rematch = false;

    /**
     * Constructs a new Client with the specified server address and port.
     *
     * @param address The server address.
     * @param port    The port number.
     * @throws IOException If an I/O error occurs during the connection setup.
     */
    protected Client(String address, int port, ClientTUI tui) throws IOException {
        clientConnection = new ClientConnection(address, port);
        clientConnection.setChatClient(this);
        this.tui = tui;

    }

    /**
     * Closes the client connection to the  server.
     */
    public synchronized void close() {
        clientConnection.close();
    }

    /**
     * Sends a chat message to the  server.
     *
     * @param message The message to be sent.
     */
    public void sendChatMessage(String message) {
        clientConnection.sendChatMessage(message);
    }

    /**
     * Sends the user's username to the  server.
     *
     * @param name The username to be sent.
     */
    public void sendUsername(String name) {
        clientConnection.sendUsername(name);
    }

    /**
     * Handles disconnection events from the server.
     * Notifies all registered listeners about the disconnection.
     */
    public void handleDisconnect() {
        for (ClientListener l : listeners) {
            l.connectionLost();
        }
    }

    /**
     * Adds a listener to the set of listeners.
     *
     * @param listener The listener to be added.
     */
    public void addListener(ClientListener listener) {
        listeners.add(listener);
    }

    /**
     * Starts the client connection to the server.
     */
    public void start() {
        clientConnection.start();
    }

    /**
     * Removes a listener from the set of listeners.
     *
     * @param listener The listener to be removed.
     */
    public void removeListener(ClientListener listener) {
        listeners.remove(listener);
    }

    public void sendMessage(String message) { clientConnection.sendChatMessage(message); }

    public GameDnB getGame() {
        return game;
    }

    public void setGame(GameDnB game) {
        this.game = game;
    }
}