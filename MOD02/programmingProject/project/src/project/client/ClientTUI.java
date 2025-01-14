package project.client;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.concurrent.TimeUnit;
import project.game.model.Move;
import project.server.Protocol;

/**
 * Represents the client and implements ClientListener.
 * Creates user-friendly access for the server
 */
public class ClientTUI implements ClientListener {
    private int inQueue = 1; // needs to control if the user is in a queue (>0) or not(<0)


    public static void main(String[] args) throws IOException, InterruptedException {
        ClientTUI clientTUI = new ClientTUI();
        clientTUI.runTUI();
    }

    private void runTUI() throws IOException, InterruptedException {
        String message;
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        System.out.println("Enter port:");
        int port = Integer.parseInt(in.readLine());
        System.out.println("Enter address:");
        String ser = in.readLine();
        Client client = new Client(ser, port, this);
        client.addListener(this);
        client.start();
        client.sendMessage(Protocol.HELLO + Protocol.SEPARATOR + "Client");
        System.out.println("Enter the username you want to play with:");
        while (!client.loggedIn) {
            String input = in.readLine();
            if (input.equalsIgnoreCase(Protocol.LIST)) {
                client.sendChatMessage(Protocol.LIST);
            } else if (input != null) {
                client.sendUsername(input);
            } else {
                System.out.println("The username shouldn't be null, please try again");
            }
            TimeUnit.MILLISECONDS.sleep(500);
        }

        help();
        while (true) {
            if (client.getGame() != null) {
                Move move = client.getGame().getTurn().determineMove(client.getGame());
                if (move != null) {
                    client.sendChatMessage(Protocol.MOVE + Protocol.SEPARATOR + move.getLocation());
                }
                continue;
            }
            if (client.rematch) {
                System.out.println(
                        "Type \"break\" to interrupt the game, or anything else to rematch");
                String command = in.readLine();
                client.rematch = false;
                if (!command.equalsIgnoreCase("break")) {
                    inQueue *= -1;
                    client.sendChatMessage(Protocol.QUEUE);
                } else {
                    client.playAI = null;
                }
            }
            System.out.println("Enter the command: ");
            message = in.readLine();
            String[] split = message.split(" ", 1);
            String command = split[0];
            switch (command.toLowerCase()) {
                case "list" -> client.sendChatMessage(Protocol.LIST);
                case "queue" -> {
                    if (client.getGame() != null) {
                        break;
                    }
                    inQueue *= -1;
                    if (inQueue > 0) {
                        client.sendChatMessage(Protocol.QUEUE);
                        client.playAI = null;
                        System.out.println("You have left the queue");
                        break;
                    }
                    System.out.println(
                            "Write the AI level, or anything else if you want to play by yourself");
                    String ai = in.readLine();
                    if (ai.equalsIgnoreCase("easy")) {
                        client.playAI = "EASY";
                    } else if (ai.equalsIgnoreCase("normal")) {
                        client.playAI = "NORMAL";
                    } else if (ai.equalsIgnoreCase("hard")) {
                        client.playAI = "HARD";
                    }
                    System.out.println("You are in a queue now");
                    client.sendChatMessage(Protocol.QUEUE);
                }
                case "help" -> help();
                case "quit" -> {
                    client.removeListener(this);
                    client.close();
                    System.exit(0);
                }
            }

        }
    }

    private void help() {
        System.out.println("type 'list' to see all connected players ");
        System.out.println(
                "type 'queue' to enter the queue for the game, after that you should decide whether you want ");
        System.out.println(
                "to play by yourself or choose a difficulty for AI (EASY/NORMAL/HARD), which will play instead of you");
        System.out.println("type 'help' to see all the commands available");
        System.out.println("type any number to play the move (allowed only during the game)");
        System.out.println("type 'quit' if you want to disconnect from the server\n");
    }

    @Override
    public void connectionLost() {
        System.out.println("Connection Lost");
        System.exit(0);

    }
}