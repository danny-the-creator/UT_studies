package ss.project.server;

import java.io.IOException;
import java.net.Socket;
import java.util.*;
import ss.networking.SocketServer;
import ss.project.game.model.*;
import ss.project.game.ui.DnBTUI;

/**
 * Represents a server which handles all the games.
 */
public class Server extends SocketServer {
    private final Set<ClientHandler> clients = new HashSet<>();
    private final List<ClientHandler> queue = new ArrayList<>();

    /**
     * Constructs a new ChatServer.
     *
     * @param port the port to listen on
     * @throws IOException if the server socket cannot be created, for example, because the port is already bound.
     */
    public Server(int port) throws IOException {
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
    }//good

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
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

    public synchronized void addClient(ClientHandler client) {
        clients.add(client);
    }


    public synchronized void removeClient(ClientHandler client) {
        synchronized (clients) {
            clients.remove(client);
        }
    }

    public Set<String> getNames() {
        Set<String> a = new HashSet<>();
        for (ClientHandler cl : clients) {
            if (cl.getUsername() != null) a.add(cl.getUsername());
        }
        return a;
    }

    public void sendServerCommmand(ClientHandler clientHandler, String message) {
        List<String> action = List.of(message.split(Protocol.SEPARATOR));
        if (action.get(0).equals(Protocol.HELLO)) {// a handshake

            if (!clientHandler.getHello()) {
                clientHandler.sendCHCommand(
                        Protocol.HELLO + Protocol.SEPARATOR + "Welcome to the server by Mira and Danil");
                clientHandler.trueHello();
            } else { clientHandler.sendCHCommand("The connection is already established"); }
        }
        if (clientHandler.getHello()) {
            switch (action.get(0)) {
                case (Protocol.MOVE) -> {
                    Move move;
                    if (clientHandler.game == null) {
                        break;
                    }
                    if (!clientHandler.game.getTurn().getName().equals(clientHandler.getUsername())) {
                        // checks if the player who sent the message is the current player and if not sends back and error.
                        clientHandler.sendCHCommand(Protocol.ERROR+Protocol.SEPARATOR+"WAIT YOUR TURN!");
                        break;
                    }
                    try {
                        //checks if ths move is valid
                        move = clientHandler.game.checkMove(action.get(1));
                    } catch (NotValidMove | NumberFormatException e) {
                        clientHandler.sendCHCommand(Protocol.ERROR+Protocol.SEPARATOR+"WRONG MOVE! TRY AGAIN!");
                        break;
                    }
                    clientHandler.game.doMove(move);
                    clientHandler.sendCHCommand(Protocol.MOVE + Protocol.SEPARATOR + action.get(1));
                    clientHandler.getPartner().sendCHCommand(Protocol.MOVE + Protocol.SEPARATOR + action.get(1));

                    if (!clientHandler.game.isGameover()) {
                        break;
                    }
                    Player winner = clientHandler.game.getWinner();
                    if (winner == null) {
                        clientHandler.sendCHCommand(Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.DRAW);
                        clientHandler.getPartner().sendCHCommand(Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.DRAW);
                    } else {
                        clientHandler.sendCHCommand(
                                Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.VICTORY + Protocol.SEPARATOR + winner.getName());
                        clientHandler.getPartner().sendCHCommand(
                                Protocol.GAMEOVER + Protocol.SEPARATOR + Protocol.VICTORY + Protocol.SEPARATOR + winner.getName());
                    }
                }
                case (Protocol.QUEUE) -> {
                    synchronized (queue) {
                        if (queue.contains(clientHandler)) {
                            queue.remove(clientHandler);
                            break;
                        }
                        queue.add(clientHandler);
                        if (queue.size() >= 2) {
                            ClientHandler client1 = queue.get(0);
                            ClientHandler client2 = queue.get(1);
                            queue.remove(1);
                            queue.remove(0);
                            client1.setPartner(client2);
                            client2.setPartner(client1);

                            Player player1 = new HumanPlayer(client1.getUsername(),
                                                             Components.BLUE);
                            Player player2 = new HumanPlayer(client2.getUsername(), Components.RED);
                            DnBTUI tui = new DnBTUI(new GameDnB(), player1, player2);   // the constructor sets the players
                            client1.game = tui.getGame();
                            client2.game = tui.getGame();
                            System.out.println(Protocol.NEWGAME+Protocol.SEPARATOR+client1.getUsername()+Protocol.SEPARATOR+client2.getUsername());
                            clientHandler.sendCHCommand(
                                    Protocol.NEWGAME + Protocol.SEPARATOR + client1.getUsername() + Protocol.SEPARATOR + client2.getUsername());
                            clientHandler.getPartner().sendCHCommand(
                                    Protocol.NEWGAME + Protocol.SEPARATOR + client1.getUsername() + Protocol.SEPARATOR + client2.getUsername());
                        }
                    }
                }
                case (Protocol.LIST) -> {
                    String names = Protocol.LIST;
                    for (ClientHandler client : clients) {
                        if (client.getUsername()!=null){    // sends all the players, who have usernames
                            names += Protocol.SEPARATOR + client.getUsername();
                        }
                    }
                    clientHandler.sendCHCommand(names);
                }
            }
        }
    }

    public static void main(String[] args) throws IOException {
        System.out.println("Enter a port for the server");
        Scanner in = new Scanner(System.in);
        int port = in.nextInt();
        Server server = new Server(port);
        System.out.println("The port of the server is: " + server.getPort());
        server.acceptConnections();
    }
}
