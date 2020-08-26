// Compiled on Ubuntu 18.04 Manticore Docker image with
//   gcc -static symbolic_read_count.c -o symbolic_read_count

#include <stdio.h>
#include <stdlib.h>
#include <netinet/in.h>

#define PORT 8081
#define BUFFER_SIZE 4

int main() {
    int server_fd, new_client;
    struct sockaddr_in address;

    // create socket file descriptor, attach to 8081
    int opt = 1; // Reuse address
    server_fd = socket(AF_INET, SOCK_STREAM, 0);
    if (setsockopt(server_fd, SOL_SOCKET, SO_REUSEADDR | SO_REUSEPORT, &opt, sizeof(opt)))
        return -1;
    address.sin_family = AF_INET;
    address.sin_addr.s_addr = INADDR_ANY;
    address.sin_port = htons(PORT);
    if (bind(server_fd, (struct sockaddr *)&address, sizeof(address)))
        return -1;

    printf("Listening on port %i...\n", PORT);


    char buffer[BUFFER_SIZE];

    int addrlen = sizeof(address);
    listen(server_fd, 10);
    new_client = accept(server_fd, (struct sockaddr *)&address, (socklen_t *)&addrlen);

    ssize_t num_rcv = recv(new_client, buffer, BUFFER_SIZE, 0);
    if (num_rcv < BUFFER_SIZE) {
      printf("Received less than BUFFER_SIZE\n");
    }
}
