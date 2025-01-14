package ss.week7.chat.server;

import java.util.*;
import ss.networking.SocketServer;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;
import ss.week7.chat.protocol.Protocol;

public class ChatServer extends SocketServer {
    private static ChatServer chatServer;
    private Set<ClientHandler> clients = new HashSet<>();
    /**
     * Constructs a new ChatServer
     * @param port the port to listen on
     * @throws IOException if the server socket cannot be created, for example, because the port is already bound.
     */
    public ChatServer(int port) throws IOException {
        super(port);
    }

    /**
     * Returns the port on which this server is listening for connections.
     *
     * @return the port on which this server is listening for connections
     */
    @Override
    public int getPort() {
        return super.getPort();
    }

    /**
     * Accepts connections and starts a new thread for each connection.
     * This method will block until the server socket is closed, for example by invoking closeServerSocket.
     *
     * @throws IOException if an I/O error occurs when waiting for a connection
     */
    @Override
    public void acceptConnections() throws IOException {
        super.acceptConnections();
    }

    /**
     * Closes the server socket. This will cause the server to stop accepting new connections.
     * If called from a different thread than the one running acceptConnections, then that thread will return from
     * acceptConnections.
     */
    @Override
    public synchronized void close() {
        super.close();
    }

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
     * @return the connection handler
     */
    @Override
    protected void handleConnection(Socket socket) {
        ServerConnection serverConnection;
        ClientHandler client;
        try {
            serverConnection = new ServerConnection(socket);
            client = new ClientHandler(serverConnection, this);
            serverConnection.setClientHandler(client);
            addClient(client);

        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        serverConnection.start();
    }
    public synchronized void addClient(ClientHandler client){
        clients.add(client);
    }
    public synchronized void removeClient(ClientHandler client){
        clients.remove(client);
    }
    public synchronized void sendChatMessage(ClientHandler clientHandler, String message){
        for (ClientHandler client : clients){
            client.sendChatMessage(clientHandler.getUsername(), message);
        }
        System.out.println(Protocol.FROM + Protocol.SEPARATOR + clientHandler.getUsername() + Protocol.SEPARATOR + message);
    }

    public static void main(String[] args) throws IOException {
        Scanner in = new Scanner(System.in);
        int port = in.nextInt();
        chatServer = new ChatServer(port);
        System.out.println(chatServer.getPort());
        chatServer.acceptConnections();
    }
}