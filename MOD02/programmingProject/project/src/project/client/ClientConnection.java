package project.client;

import java.io.IOException;
import project.game.ai.ComputerPlayer;
import project.game.ai.StrategyLvlEasy;
import project.game.ai.StrategyLvlHard;
import project.game.ai.StrategyLvlNormal;
import project.game.model.*;
import project.game.ui.DnBTUI;
import project.server.Protocol;

/**
 * Receives the messages from the server and determines actions,
 * that need to be taken based on the message.
 */
public class ClientConnection extends SocketConnection {
    Client client;
    String name = null;

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
        String[] commands = message.split(Protocol.SEPARATOR);
        switch (commands[0]) {
            case Protocol.HELLO -> System.out.println(commands[1]);
            case Protocol.LIST -> {
                System.out.println("The following players are on the server now:");
                for (int i = 1; commands.length > i; i++) {
                    System.out.println(commands[i]);
                }
            }
            case Protocol.LOGIN -> {
                System.out.println("You were successfully logged in");
                client.loggedIn = true;
            }
            case Protocol.ALREADYLOGGEDIN -> {
                System.out.println(
                        "The user with that name already exists, please try another username");
                System.out.println("You can see the list of already existing names by typing list");
                this.name = null;
            }
            case Protocol.MOVE -> {
                client.getGame().doMove(new MoveDnB(client.getGame().getTurn().getColour(),
                                                    Integer.parseInt(commands[1])));
                System.out.println(client.getGame().toString());
            }
            case Protocol.GAMEOVER -> {
                switch (message.split(Protocol.SEPARATOR)[1]) {
                    case Protocol.DISCONNECT -> System.out.println(
                            "Your opponent has disconnected from the game. You won!");
                    case Protocol.VICTORY -> System.out.println("The player " + message.split(
                            Protocol.SEPARATOR)[2] + " won the game!");
                    case Protocol.DRAW -> System.out.println("The game ended with a draw");
                }
                client.setGame(null);
                client.rematch = true; // shows that the player can be asked for the rematch.
                System.out.println("Type ENTER to continue");
            }
            case Protocol.NEWGAME -> {
                Player player = null;
                String colour1;
                String colour2;
                DnBTUI tui;
                if (name.equals(commands[1])) {
                    colour1 = Components.BLUE;
                    colour2 = Components.RED;
                } else {
                    colour1 = Components.RED;
                    colour2 = Components.BLUE;
                }
                if (client.playAI == null) {
                    player = new HumanPlayer(name, colour1);
                } else if (client.playAI.equals("EASY")) {
                    player = new ComputerPlayer(colour1, new StrategyLvlEasy());
                } else if (client.playAI.equals("NORMAL")) {
                    player = new ComputerPlayer(colour1, new StrategyLvlNormal());
                } else if (client.playAI.equals("HARD")) {
                    player = new ComputerPlayer(colour1, new StrategyLvlHard());
                }
                if (name.equals(commands[1])) {
                    tui = new DnBTUI(new GameDnB(), player, new HumanPlayer(commands[2], colour2));
                } else {
                    tui = new DnBTUI(new GameDnB(), new HumanPlayer(commands[1], colour2), player);
                }
                client.setGame(tui.getGame());
                System.out.println(tui.getGame().toString());
                System.out.println("Type ENTER to start the game");
            }
            case Protocol.ERROR -> System.out.println("!ERROR!");

        }
    }

    /**
     * Handles disconnection events from the  server.
     */
    @Override
    protected void handleDisconnect() {
        client.handleDisconnect();

    }

    /**
     * Closes the client connection to the  server.
     */
    public void close() {
        super.close();
    }

    /**
     * Sends a chat message to the  server.
     *
     * @param message The message to be sent.
     */
    public void sendChatMessage(String message) {
        super.sendMessage(message);
    }

    /**
     * Sends the user's username to the  server.
     *
     * @param name The username to be sent.
     */
    public void sendUsername(String name) {
        if (this.name == null) {
            this.name = name;
        }
        super.sendMessage(Protocol.LOGIN + Protocol.SEPARATOR + name);
    }

    /**
     * Sets the associated Client for handling events.
     *
     * @param client The Client instance to be associated with this connection.
     */
    public void setChatClient(Client client) {
        this.client = client;

    }
}
